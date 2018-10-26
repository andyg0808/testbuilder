"""
Produces a list of line numbers present in an SSA AST
"""
from functools import partial
from typing import Any, List

from toolz import pipe

from . import nodetree as n, ssa_basic_blocks as sbb
from .visitor import GatherVisitor


class LineSplitter(GatherVisitor[int]):
    def visit(self, v: Any, *args: Any, **kwargs: Any) -> List[int]:
        _filter_high = partial(filter, lambda i: i >= 0)
        return pipe(v, super().visit, set, _filter_high, sorted)

    def visit_Stmt(self, node: n.stmt) -> List[int]:
        return [node.line]

    def visit_Expr(self, node: n.Expr) -> List[int]:
        # Don't create tests centered on non-function-call `Expr`s,
        # because there is nothing to target on those lines.
        if isinstance(node.value, n.Call):
            return [node.line]
        else:
            return []
