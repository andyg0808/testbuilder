from functools import partial, singledispatch
from pathlib import Path
from typing import Generator, List, Optional, Set, TypeVar, cast

import z3
from astor import to_source  # type: ignore
from logbook import Logger
from toolz import mapcat, pipe
from visitor import SetGatherVisitor, SimpleVisitor

from . import converter, nodetree as n, ssa_basic_blocks as sbb
from .function_substituter import FunctionSubstitute
from .iter_monad import liftIter
from .linefilterer import filter_lines
from .phifilter import PhiFilterer
from .ssa_repair import repair
from .store import Store
from .type_manager import TypeManager
from .type_registrar import TypeRegistrar
from .type_union import TypeUnion
from .utils import dataclass_dump
from .z3_types import BOOL_TRUE, bool_all, bool_any

log = Logger("ssa_to_expression")

Expression = z3.ExprRef
StopBlock = Optional[sbb.BasicBlock]
BoolList = List[z3.BoolRef]

T = TypeVar("T")


class SSAVisitor(SimpleVisitor[BoolList]):
    def __init__(self, registrar: TypeRegistrar, module: sbb.Module) -> None:
        self.module = module
        self.type_manager = TypeManager()
        self.registrar = registrar
        self.store = Store(self.registrar)
        self.expression = converter.ExpressionConverter(
            self.registrar, self.type_manager, self.store
        )

    def visit_Code(self, node: sbb.Code, stop: StopBlock) -> BoolList:
        if stop and node.number == stop.number:
            return []

        exprs = self.visit(node.parent, stop)
        visited = list(mapcat(self.visit, node.code))
        res = exprs + visited
        return res

    def visit_StartBlock(self, node: sbb.StartBlock, stop: StopBlock) -> BoolList:
        return []

    def visit_ReturnBlock(self, node: sbb.ReturnBlock, stop: StopBlock) -> BoolList:
        if len(node.parents) == 1:
            return self.visit(node.parents[0], stop)
        exprs = []
        types = []
        for parent in node.parents:
            self.type_manager.push()
            parent_exprs = self.visit(parent, stop)
            exprs.append(bool_all(parent_exprs))
            types.append(self.type_manager.pop())
        self.type_manager.merge_and_update(types)
        return [bool_any(exprs)]

    def visit_Stmt(self, node: n.stmt) -> BoolList:
        union = self.expression(node)
        if union.is_bool():
            exprs: BoolList = [union.to_expr()]
        else:
            # The expression is not a boolean. This can happen when
            # assigning to an attribute, since the actual assignment
            # occurs in the store, not to the variable itself. If the
            # variable storing the reference did not already exist,
            # however, it will be restricted to a reference.
            exprs = [union.implications()]
        if self.store.pending():
            exprs.append(self.store.write())
        return exprs

    def visit_BlockTree(self, node: sbb.BlockTree) -> BoolList:
        exprs = self.visit(node.end, None)
        assert not self.store.pending(), "Store pending at highest level"
        return exprs

    def visit_Conditional(self, node: sbb.Conditional, stop: StopBlock) -> BoolList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        branches: List[List[z3.BoolRef]] = []
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

        # print("branches", branches)

        filled_branches = filter(lambda x: x, branches)
        return code + [pipe(filled_branches, liftIter(bool_all), bool_any)]

    def visit_Loop(self, node: sbb.Loop, stop: StopBlock) -> BoolList:
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
                    branches.append([BOOL_TRUE])
                else:
                    branches.append(res)
        if branches:
            branch_expr: BoolList = [pipe(branches, liftIter(bool_all), bool_any)]
            self.type_manager.merge_and_update(types)
        else:
            branch_expr = []
        return code + branch_expr

    def visit_TrueBranch(self, node: sbb.TrueBranch, stop: StopBlock) -> BoolList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        return code + [self.to_boolean(self.expression(node.conditional))]

    def visit_FalseBranch(self, node: sbb.FalseBranch, stop: StopBlock) -> BoolList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        return code + [self.to_boolean(self.expression(node.conditional), invert=True)]

    def to_boolean(self, value: TypeUnion, invert: bool = False) -> z3.BoolRef:
        if value.is_bool():
            return value.to_expr(invert)
        else:
            return self.store.to_boolean(value, invert).to_expr()


@singledispatch
def process(filepath: Path, node: object, visitor: SSAVisitor) -> sbb.TestData:
    """
    Convert a node to a TestData description

    Handles both the case of a function and inline code
    """
    raise RuntimeError(f"process not implemented for {type(node)}")


@process.register(sbb.FunctionDef)
def process_fut(
    node: sbb.FunctionDef, filepath: Path, visitor: SSAVisitor
) -> sbb.TestData:
    if node.blocks.empty():
        expression = BOOL_TRUE
    else:
        expressions = visitor.visit(node.blocks)
        for expr in expressions:
            assert z3.is_bool(expr), f"{expr} is not boolean"
        expression = bool_all(expressions)
    free_variables = [sbb.Variable(arg) for arg in node.args]
    return sbb.TestData(
        filepath=filepath,
        name=node.name,
        free_variables=free_variables,
        expression=expression,
        source_text=to_source(node.original),
    )


@process.register(sbb.BlockTree)
def process_sut(
    code: sbb.BlockTree, filepath: Path, visitor: SSAVisitor
) -> sbb.TestData:
    if code.empty():
        expression = BOOL_TRUE
    else:
        expression = bool_all(visitor.visit(code))
    free_variables = find_variables(code)
    return sbb.TestData(
        filepath=filepath,
        name="code",
        free_variables=free_variables,
        expression=expression,
        source_text="<source missing>",
    )


class VariableFinder(SetGatherVisitor[sbb.Variable]):
    def visit_Set(self, stmt: n.Set) -> Set[sbb.Variable]:
        return set()

    def visit_Name(self, expr: n.Name) -> Set[sbb.Variable]:
        if expr.set_count == 0:
            return {sbb.Variable(expr.id)}
        else:
            return set()


def find_variables(code: sbb.BlockTree) -> List[sbb.Variable]:
    return list(VariableFinder()(code))


def ssa_to_expression(
    filepath: Path, registrar: TypeRegistrar, request: sbb.Request
) -> sbb.TestData:
    assert isinstance(request, sbb.Request)
    # TODO: I think this is right?
    v = SSAVisitor(registrar, request.module)
    assert isinstance(request.code, sbb.BlockTree) or isinstance(
        request.code, sbb.FunctionDef
    )
    return process(request.code, filepath, v)


def ssa_lines_to_expression(
    filepath: Path,
    registrar: TypeRegistrar,
    target_line: int,
    slice: bool,
    module: sbb.Module,
) -> Optional[sbb.TestData]:
    request = filter_lines(target_line, module, slice)

    log.debug("Filtered request {}", dataclass_dump(request))
    if request is None:
        return None
    repaired_request: sbb.Request = pipe(
        request, repair, PhiFilterer(), FunctionSubstitute()
    )
    return ssa_to_expression(filepath, registrar, repaired_request)
