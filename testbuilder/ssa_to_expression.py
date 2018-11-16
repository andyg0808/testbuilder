from functools import singledispatch
from typing import List, Optional, cast

from astor import to_source  # type: ignore
from toolz import mapcat, pipe

import z3

from . import converter, nodetree as n, ssa_basic_blocks as sbb
from .function_substituter import FunctionSubstitute
from .iter_monad import liftIter
from .linefilterer import filter_lines
from .phifilter import PhiFilterer
from .ssa_repair import repair
from .store import Store
from .test_utils import write_dot
from .type_manager import TypeManager
from .type_registrar import TypeRegistrar
from .type_union import TypeUnion
from .visitor import GatherVisitor, SimpleVisitor
from .z3_types import bool_all, bool_any, bool_true

Expression = z3.ExprRef
StopBlock = Optional[sbb.BasicBlock]
ExprList = List[Expression]


class SSAVisitor(SimpleVisitor[ExprList]):
    def __init__(self, registrar: TypeRegistrar, module: sbb.Module) -> None:
        self.module = module
        self.type_manager = TypeManager()
        self.registrar = registrar
        self.store = Store(self.registrar)
        self.expression = converter.ExpressionConverter(
            self.registrar, self.type_manager, self.store
        )

    def visit_Code(self, node: sbb.Code, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        exprs = self.visit(node.parent, stop)
        visited = list(mapcat(self.visit, node.code))
        res = exprs + visited
        return res

    def visit_StartBlock(self, node: sbb.StartBlock, stop: StopBlock) -> ExprList:
        return []

    def visit_ReturnBlock(self, node: sbb.ReturnBlock, stop: StopBlock) -> ExprList:
        if len(node.parents) == 1:
            return self.visit(node.parents[0], stop)
        exprs = []
        for parent in node.parents:
            parent_exprs = cast(List[z3.Bool], self.visit(parent, stop))
            exprs.append(bool_all(parent_exprs))

        return [bool_any(exprs)]

    def visit_Stmt(self, node: n.stmt) -> ExprList:
        union = self.expression(node)
        if union.is_bool():
            exprs: List[Expression] = [union.to_expr()]
        else:
            # The union is not a boolean; the only supported case this
            # could happen would be a bare expression, and the only
            # side-effectful expression is yield, which is
            # unsupported.
            exprs = [union.implications()]
        if self.store.pending():
            exprs.append(self.store.write())
        return exprs

    def visit_BlockTree(self, node: sbb.BlockTree) -> ExprList:
        return self.visit(node.end, None)

    def visit_Conditional(self, node: sbb.Conditional, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        print("node.parent", node.parent, id(node.parent))
        branches = []
        types = []
        if node.true_branch:
            self.type_manager.push()
            branches.append(self.visit(node.true_branch, node.parent))
            types.append(self.type_manager.pop())
        if node.false_branch:
            self.type_manager.push()
            branches.append(self.visit(node.false_branch, node.parent))
            types.append(self.type_manager.pop())
        self.type_manager.merge_and_update(types)

        print("branches", branches)

        return code + [pipe(branches, liftIter(bool_all), bool_any)]

    def visit_Loop(self, node: sbb.Loop, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)
        branches = []
        types = []
        for branch in node.loops:
            self.type_manager.push()
            res = self.visit(branch, node.parent)
            types.append(self.type_manager.pop())
            if res is not None:
                if len(res) == 0:
                    # This can happen if no assignments occur in a
                    # loop. Then the bypass doesn't even have a
                    # phi-fixing assignment, and it ends up completely
                    # empty. By using True as a result, we avoid
                    # making `bool_all` angry when deciding what to do
                    # with this branch.
                    branches.append([bool_true()])
                else:
                    branches.append(res)
        if branches:
            branch_expr: ExprList = [pipe(branches, liftIter(bool_all), bool_any)]
            self.type_manager.merge_and_update(types)
        else:
            branch_expr = []
        return code + branch_expr

    def visit_TrueBranch(self, node: sbb.TrueBranch, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        return code + [self.to_boolean(self.expression(node.conditional))]

    def visit_FalseBranch(self, node: sbb.FalseBranch, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        return code + [self.to_boolean(self.expression(node.conditional), invert=True)]

    def to_boolean(self, value: TypeUnion, invert: bool = False) -> z3.Bool:
        if value.is_bool():
            return value.to_expr(invert)
        else:
            return self.registrar.to_boolean(value, invert).to_expr()


@singledispatch
def process(node: object, visitor: SSAVisitor) -> sbb.TestData:
    """
    Convert a node to a TestData description

    Handles both the case of a function and inline code
    """
    raise RuntimeError(f"process not implemented for {type(node)}")


@process.register(sbb.FunctionDef)
def process_fut(node: sbb.FunctionDef, visitor: SSAVisitor) -> sbb.TestData:
    if node.blocks.empty():
        expression = bool_true()
    else:
        expressions = visitor.visit(node.blocks)
        for expr in expressions:
            assert z3.is_bool(expr), f"{expr} is not boolean"
        expression = bool_all(cast(List[z3.Bool], expressions))
    free_variables = [sbb.Variable(arg) for arg in node.args]
    return sbb.TestData(
        name=node.name,
        free_variables=free_variables,
        expression=expression,
        source_text=to_source(node.original),
    )


@process.register(sbb.BlockTree)
def process_sut(code: sbb.BlockTree, visitor: SSAVisitor) -> sbb.TestData:
    if code.empty():
        expression = bool_true()
    else:
        expression = bool_all(cast(List[z3.Bool], visitor.visit(code)))
    free_variables = find_variables(code)
    return sbb.TestData(
        name="code",
        free_variables=free_variables,
        expression=expression,
        source_text="<source missing>",
    )


class VariableFinder(GatherVisitor[sbb.Variable]):
    def visit_Set(self, stmt: n.Set) -> List[sbb.Variable]:
        return []

    def visit_Name(self, expr: n.Name) -> List[sbb.Variable]:
        if expr.set_count == 0:
            return [sbb.Variable(expr.id)]
        else:
            return []


def find_variables(code: sbb.BlockTree) -> List[sbb.Variable]:
    return VariableFinder().visit(code)


def ssa_to_expression(registrar: TypeRegistrar, request: sbb.Request) -> sbb.TestData:
    assert isinstance(request, sbb.Request)
    # TODO: I think this is right?
    v = SSAVisitor(registrar, request.module)
    assert isinstance(request.code, sbb.BlockTree) or isinstance(
        request.code, sbb.FunctionDef
    )
    return process(request.code, v)


def ssa_lines_to_expression(
    registrar: TypeRegistrar, target_line: int, module: sbb.Module
) -> Optional[sbb.TestData]:
    write_dot(module, "showdot.dot")
    request = filter_lines(target_line, module)
    if request is None:
        return None
    repaired_request: sbb.Request = pipe(
        request, repair, PhiFilterer(), FunctionSubstitute()
    )
    write_dot(repaired_request, "showdot.dot")
    return ssa_to_expression(registrar, repaired_request)
