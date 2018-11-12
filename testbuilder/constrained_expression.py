from typing import Generic, List, Tuple, TypeVar, cast

import z3
from dataclasses import dataclass, field

from .z3_types import Expression, bool_and, bool_not

E = TypeVar("E", bound=Expression)
VarConstraint = Tuple[str, z3.SortRef, z3.Bool]


@dataclass
class ConstrainedExpression:
    expr: Expression
    constraints: List[VarConstraint] = field(default_factory=list)

    def constrained(self) -> bool:
        return len(self.constraints) > 0

    def constraint(self) -> z3.Bool:
        assert self.constrained(), "Cannot get constraint for unconstrained expression"
        return bool_and(constraint for name, sort, constraint in self.constraints)

    def to_expr(self, invert: bool = False) -> Expression:
        expr: Expression = self.expr
        if invert:
            assert expr.sort() == z3.BoolSort(), (
                "Cannot invert a ConstrainedExpression which"
                " doesn't have a boolean value"
            )
            expr = bool_not(cast(z3.Bool, expr))
        if self.constrained():
            assert self.expr.sort() == z3.BoolSort(), (
                "Cannot to_expr a ConstrainedExpression with constraints"
                " which doesn't have a boolean expr"
            )
            return bool_and([cast(z3.Bool, expr), self.constraint()])
        else:
            return expr
