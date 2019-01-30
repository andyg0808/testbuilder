from dataclasses import dataclass, field
from typing import Generic, List, Set, Tuple, TypeVar, cast

import z3

from .z3_types import Expression, bool_and, bool_not

E = TypeVar("E", bound=Expression)
VarConstraint = Tuple[str, z3.SortRef, z3.BoolRef]
ConstraintSet = Set[VarConstraint]


@dataclass
class ConstrainedExpression:
    expr: Expression
    constraints: ConstraintSet = field(default_factory=set)

    def constrained(self) -> bool:
        return len(self.constraints) > 0

    def constraint(self) -> z3.BoolRef:
        assert self.constrained(), "Cannot get constraint for unconstrained expression"
        constraint_list = list(self.constraints)
        constraint_list.sort(key=lambda x: x[0])
        return bool_and(constraint for name, sort, constraint in constraint_list)

    def to_expr(self, invert: bool = False) -> Expression:
        expr: Expression = self.expr
        if invert:
            assert expr.sort() == z3.BoolSort(), (
                "Cannot invert a ConstrainedExpression which"
                " doesn't have a boolean value"
            )
            expr = bool_not(cast(z3.BoolRef, expr))
        if self.constrained():
            assert self.expr.sort() == z3.BoolSort(), (
                "Cannot to_expr a ConstrainedExpression with constraints"
                " which doesn't have a boolean expr"
            )
            return bool_and([cast(z3.BoolRef, expr), self.constraint()])
        else:
            return expr
