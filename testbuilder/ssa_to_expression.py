from functools import singledispatch
from typing import List, Optional, Set

from toolz import mapcat, pipe

import z3

from . import converter, nodetree as n, ssa_basic_blocks as sbb
from .expression_builder import ExprList, bool_and, bool_not, bool_or, to_boolean
from .iter_monad import liftIter
from .linefilterer import filter_lines
from .phifilter import PhiFilterer
from .ssa_repair import repair
from .visitor import GatherVisitor, SimpleVisitor

Expression = z3.ExprRef
StopBlock = Optional[sbb.BasicBlock]


class SSAVisitor(SimpleVisitor[ExprList]):
    def __init__(self, module: sbb.Module) -> None:
        self.module = module

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
        exprs = []
        for parent in node.parents:
            exprs.append(bool_all(self.visit(parent, stop)))

        return [bool_any(exprs)]

    def visit_Stmt(self, node: n.stmt) -> ExprList:
        return [converter.visit_expr(node)]

    def visit_BlockTree(self, node: sbb.BlockTree) -> ExprList:
        return self.visit(node.end, None)

    def visit_Conditional(self, node: sbb.Conditional, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        print("node.parent", node.parent, id(node.parent))
        branches = []
        if node.true_branch:
            branches.append(self.visit(node.true_branch, node.parent))
        if node.false_branch:
            branches.append(self.visit(node.false_branch, node.parent))

        print("branches", branches)

        return code + [pipe(branches, liftIter(bool_all), bool_any)]

    def visit_Loop(self, node: sbb.Loop, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)
        branches = [self.visit(branch, node.parent) for branch in node.loops]
        branches = [b for b in branches if b]
        if branches:
            branch_expr: ExprList = [pipe(branches, liftIter(bool_all), bool_any)]
        else:
            branch_expr = []
        return code + branch_expr

    def visit_TrueBranch(self, node: sbb.TrueBranch, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        return code + [to_boolean(converter.visit_expr(node.conditional))]

    def visit_FalseBranch(self, node: sbb.FalseBranch, stop: StopBlock) -> ExprList:
        if stop and node.number == stop.number:
            return []

        code = self.visit(node.parent, stop)

        return code + [bool_not(to_boolean(converter.visit_expr(node.conditional)))]


@singledispatch
def process(node: object, visitor: SSAVisitor) -> sbb.TestData:
    raise RuntimeError(f"process not implemented for {type(node)}")


@process.register(sbb.FunctionDef)
def process_fut(node: sbb.FunctionDef, visitor: SSAVisitor) -> sbb.TestData:
    if node.blocks.empty():
        expression = bool_true()
    else:
        expression = bool_all(visitor.visit(node.blocks))
    free_variables = [sbb.Variable(arg) for arg in node.args]
    return sbb.TestData(
        name=node.name, free_variables=free_variables, expression=expression
    )


@process.register(sbb.BlockTree)
def process_sut(code: sbb.BlockTree, visitor: SSAVisitor) -> sbb.TestData:
    if code.empty():
        expression = bool_true()
    else:
        expression = bool_all(visitor.visit(code))
    free_variables = find_variables(code)
    return sbb.TestData(
        name="code", free_variables=free_variables, expression=expression
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


def bool_all(exprs: List[Expression]) -> Expression:
    exprs = list(exprs)
    if len(exprs) > 1:
        return bool_and(*exprs)
    elif len(exprs) == 1:
        return exprs[0]
    else:
        raise RuntimeError("Taking all of no exprs")


def bool_any(exprs: List[Expression]) -> Expression:
    """
    Allow any path in exprs to be taken. If only one path is present,
    it is required. No exprs results in an exception.
    """
    exprs = list(exprs)
    if len(exprs) > 1:
        return bool_or(*exprs)
    elif len(exprs) == 1:
        return exprs[0]
    else:
        raise RuntimeError("Taking any of no exprs")


def bool_true() -> Expression:
    return z3.BoolVal(True)


def ssa_to_expression(request: sbb.Request) -> sbb.TestData:
    assert isinstance(request, sbb.Request)
    # TODO: I think this is right?
    v = SSAVisitor(request.module)
    assert isinstance(request.code, sbb.BlockTree) or isinstance(
        request.code, sbb.FunctionDef
    )
    return process(request.code, v)


def ssa_lines_to_expression(
    target_line: int, lines: Set[int], module: sbb.Module
) -> sbb.TestData:
    from .test_utils import write_dot

    write_dot(module, "showdot.dot")
    request = filter_lines(target_line, lines, module)

    repaired_request: sbb.Request = pipe(request, repair, PhiFilterer())

    write_dot(repaired_request, "showdot.dot")
    return ssa_to_expression(repaired_request)
