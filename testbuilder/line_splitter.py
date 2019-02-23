"""
Produces a list of line numbers present in an SSA AST
"""
from typing import Any, Generator, Iterable, List, Set

from . import nodetree as n
from .visitor import SetGatherVisitor


def line_splitter(obj: Any) -> List[int]:
    splitter = LineSplitter()
    splits = splitter(obj)
    filtered = filter_high(splits)
    return sorted(filtered)


class LineSplitter(SetGatherVisitor[int]):
    def visit_Stmt(self, node: n.stmt) -> Set[int]:
        return {node.line}

    def visit_Expr(self, node: n.Expr[Any]) -> Set[int]:
        # Don't create tests centered on non-function-call `Expr`s,
        # because there is nothing to target on those lines.
        if isinstance(node.value, n.Call):
            return {node.line}
        else:
            return set()


def filter_high(vals: Iterable[int]) -> Generator[int, None, None]:
    for i in vals:
        if i >= 0:
            yield i
