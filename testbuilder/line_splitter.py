"""
Produces a list of line numbers present in an SSA AST
"""
from functools import partial
from typing import List

from toolz import pipe

from . import nodetree as n, ssa_basic_blocks as sbb
from .visitor import GatherVisitor


class LineSplitter(GatherVisitor[int]):
    def visit_Module(self, node: sbb.Module) -> List[int]:
        _filter_high = partial(filter, lambda i: i >= 0)
        return pipe(node, self.generic_visit, set, _filter_high, sorted)

    def visit_Stmt(self, node: n.stmt) -> List[int]:
        return [node.line]

    # def visit_Controlled(self, node: sbb.Controlled) -> List[int]:
    #     return [node.line] + self.generic_visit(node)
