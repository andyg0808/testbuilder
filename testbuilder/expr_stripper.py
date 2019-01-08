"""
Drops lines which only contain bare expressions which are not function
calls.
"""
from typing import Optional

from logbook import Logger

from . import nodetree as n, ssa_basic_blocks as sbb
from .visitor import UpdateVisitor

log = Logger("expr_stripper")


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

    def visit_Expr(self, expr: n.Expr) -> Optional[n.Expr]:
        if not isinstance(expr.value, n.Call):
            log.debug(f"Discarding {expr}")
            # Discard code which is not a call site
            return None
        return self.generic_visit(expr)
