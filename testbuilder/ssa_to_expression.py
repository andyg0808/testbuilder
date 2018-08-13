from functools import partial, singledispatch
from typing import List, Union

from toolz import pipe

import z3
from dataclasses import dataclass

from . import basic_block as bb, converter, nodetree as n, ssa_basic_blocks as sbb
from .basic_block import BlockTree
from .expression_builder import ExprList, VarMapping
from .iter_monad import chain

Expression = z3.ExprRef


@singledispatch
def visit(thing: sbb.BasicBlock, depth: int, module: sbb.Module) -> ExprList:
    raise RuntimeError(f"No handler for {type(thing)}")


@visit.register(n.expr)
def visit_expr(node: n.expr) -> ExprList:
    return [converter.visit_expr(node)]


def visit_FunctionDef(function: sbb.FunctionDef) -> ExprList:
    pass


@visit.register(sbb.Code)
def visit_Code(node: sbb.Code, depth: int, module: sbb.Module) -> ExprList:
    exprs = visit(node.parent, depth, module)


@dataclass
class Request:
    module: sbb.Module
    code: sbb.BasicBlock


def ssa_to_expression(depth: int, request: Request) -> ExprList:
    assert isinstance(request, Request)
    # TODO: I think this is right?
    _visit = partial(visit, depth=depth, module=request.module)
    return _visit(request.code)


def blocktree_and_ssa_to_expression(
    depth: int, tree: BlockTree, module: sbb.Module, variables: VarMapping
) -> ExprList:
    from .basic_block_to_ssa import visit as basic_block_to_ssa

    code = basic_block_to_ssa(tree.target, {}, variables)
    return ssa_to_expression(depth, Request(module, code))
