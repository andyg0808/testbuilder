"""
Produces a list of line numbers present in an SSA AST
"""
from typing import List

from . import nodetree as n, ssa_basic_blocks as sbb
from .visitor import GatherVisitor


class LineSplitter(GatherVisitor[int]):
    def visit_Stmt(self, node: n.stmt) -> List[int]:
        return [node.line]

    # def visit_Controlled(self, node: sbb.Controlled) -> List[int]:
    #     return [node.line] + self.generic_visit(node)
