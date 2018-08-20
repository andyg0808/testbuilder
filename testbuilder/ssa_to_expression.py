from functools import partial, reduce, singledispatch
from typing import List, MutableMapping as MMapping, Optional, Set, Union

from toolz import mapcat, pipe

import z3
from dataclasses import dataclass

from . import basic_block as bb, converter, nodetree as n, ssa_basic_blocks as sbb
from .basic_block import BlockTree
from .expression_builder import (
    ExprList,
    VarMapping,
    bool_and,
    bool_not,
    bool_or,
    to_boolean,
)
from .iter_monad import chain, liftIter
from .linefilterer import filter_lines
from .ssa_repair import repair
from .utils import crash
from .visitor import GenericVisitor, SimpleVisitor

Expression = z3.ExprRef
StopBlock = Optional[sbb.BasicBlock]


class SSAVisitor(SimpleVisitor[ExprList]):
    def __init__(self, module: sbb.Module) -> None:
        self.module = module

    def visit_Code(self, node: sbb.Code, stop: StopBlock) -> ExprList:
        if node is stop:
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

    def visit_stmt(self, node: n.stmt) -> ExprList:
        return [converter.visit_expr(node)]

    def visit_BlockTree(self, node: sbb.BlockTree) -> ExprList:
        return self.visit(node.end, None)

    def visit_Conditional(self, node: sbb.Conditional, stop: StopBlock) -> ExprList:
        code = self.visit(node.parent, stop)

        branches = []
        if node.true_branch:
            branches.append(self.visit(node.true_branch, node.parent))
        if node.false_branch:
            branches.append(self.visit(node.false_branch, node.parent))

        print("branches", branches)

        return code + [pipe(branches, liftIter(bool_all), bool_any)]


@singledispatch
def process(node: object, visitor: SSAVisitor) -> sbb.TestData:
    raise RuntimeError(f"process not implemented for {type(node)}")


@process.register(sbb.FunctionDef)
def process_fut(node: sbb.FunctionDef, visitor: SSAVisitor) -> sbb.TestData:
    expression = bool_all(visitor.visit(node.blocks))
    free_variables = [sbb.Variable(arg) for arg in node.args]
    return sbb.TestData(
        name=node.name, free_variables=free_variables, expression=expression
    )


@process.register(sbb.BlockTree)
def process_sut(code: sbb.BlockTree, visitor: SSAVisitor) -> sbb.TestData:
    expression = bool_all(visitor.visit(code))
    free_variables = find_variables(code)
    return sbb.TestData(
        name="code", free_variables=free_variables, expression=expression
    )


class VariableFinder(GenericVisitor[sbb.Variable]):
    def visit_Set(self, stmt: n.Set) -> List[sbb.Variable]:
        return []

    def visit_Name(self, expr: n.Name) -> List[sbb.Variable]:
        if expr.set_count == 0:
            return [sbb.Variable(expr.id)]
        else:
            return []

    # def visit_BlockTree(self, tree: sbb.BlockTree) -> List[sbb.Variable]:
    #     return self.visit(tree.end)

    # def visit_ReturnBlock(self, block: sbb.ReturnBlock) -> List[sbb.Variable]:
    #     return list(mapcat(self.visit, block.parents))

    # def visit_Code(self, block: sbb.Code) -> List[sbb.Variable]:
    #     return list(mapcat(self.visit, block.code))


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


def ssa_to_expression(request: sbb.Request) -> sbb.TestData:
    assert isinstance(request, sbb.Request)
    # TODO: I think this is right?
    v = SSAVisitor(request.module)
    assert isinstance(request.code, sbb.BlockTree) or isinstance(
        request.code, sbb.FunctionDef
    )
    return process(request.code, v)


def ssa_lines_to_expression(lines: Set[int], module: sbb.Module) -> sbb.TestData:
    request = filter_lines(lines, module)
    repaired_request = repair(request)
    return ssa_to_expression(repaired_request)


# def blocktree_and_ssa_to_expression(
#     depth: int, tree: BlockTree, module: sbb.Module, variables: VarMapping
# ) -> ExprList:
#     from .basic_block_to_ssa import visit as basic_block_to_ssa

#     assert tree.target
#     code = basic_block_to_ssa(tree.target, variables)
#     from .test_utils import show_dot

#     # show_dot(code)
#     return ssa_to_expression(sbb.Request(module, code))


# @singledispatch
# def is_false_path(node: sbb.Controlled, query: sbb.BasicBlock) -> bool:
#     raise RuntimeError("Not implemented")


# @is_false_path.register(sbb.Conditional)
# def is_false_path(node: sbb.Conditional, query: sbb.BasicBlock) -> bool:
#     return node.false_branch is query


# @is_false_path.register(sbb.Loop)
# def is_false_path(node: sbb.Loop, query: sbb.BasicBlock) -> bool:
#     return node.bypass is query
