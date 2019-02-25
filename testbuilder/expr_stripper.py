"""
Drops lines which only contain bare expressions which are not function
calls.
"""
from typing import Optional, TypeVar

from logbook import Logger

from visitor import UpdateVisitor

from . import nodetree as n, ssa_basic_blocks as sbb

log = Logger("expr_stripper")

E = TypeVar("E", bound=n.expr)


class ExprStripper(UpdateVisitor):
    def visit_Code(self, node: sbb.Code) -> sbb.Code:
        code = []
        parent = self.visit(node.parent)
        for l in node.code:
            updated = self.visit(l)
            if updated is not None:
                code.append(updated)
        return sbb.Code(
            number=node.number,
            first_line=node.first_line,
            last_line=node.last_line,
            parent=parent,
            code=code,
        )

    def visit_Expr(self, expr: n.Expr[E]) -> Optional[n.Expr[E]]:
        if not isinstance(expr.value, n.Call):
            log.debug(f"Discarding {expr}")
            # Discard code which is not a call site
            return None
        return self.generic_visit(expr)
