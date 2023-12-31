from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, List, Optional, cast

import z3

from .constrained_expression import ConstrainedExpression as CExpr
from .z3_types import BOOL_TRUE, Expression, SortSet, bool_or


@dataclass(frozen=True)
class TypeUnion:
    expressions: List[CExpr]
    sorts: SortSet

    @staticmethod
    def wrap(expr: Expression) -> TypeUnion:
        """
        Wrap `expr` in an unconstrained `CExpr` and a `TypeUnion`,
        using the result of `expr.sort()` as the sort present in the
        `TypeUnion`.

        Args:
            expr: An expression to put into a type union
        """
        cexpr = CExpr(expr=expr)
        return TypeUnion([cexpr], {expr.sort()})

    def empty(self) -> bool:
        return len(self.expressions) == 0

    def is_bool(self) -> bool:
        return self.sorts == {z3.BoolSort()}

    def to_expr(self, invert: bool = False) -> z3.BoolRef:
        """
        Creates a boolean expression allowing execution to procede down
        any of the possible expressions in this TypeUnion
        """
        assert (
            self.is_bool()
        ), "Cannot convert non-boolean TypeUnion to boolean expression"
        boolexprs: List[z3.BoolRef] = [
            cast(z3.BoolRef, x.to_expr(invert)) for x in self.expressions
        ]
        return bool_or(boolexprs)

    def implications(self) -> z3.BoolRef:
        assert not self.empty()
        constraints = [x.constraint() for x in self.expressions if x.constrained()]
        if not constraints:
            return BOOL_TRUE
        return bool_or(constraints)

    def unwrap(
        self,
        choice: Optional[z3.SortRef] = None,
        constraint: Optional[Expression] = None,
    ) -> Expression:
        if choice is None:
            assert (
                len(self.sorts) <= 1
            ), f"Cannot unwrap TypeUnion with more than one type; this has {self.sorts}"
            assert len(self.expressions) < 2, (
                "Cannot unwrap TypeUnion without exactly one "
                f"value; this has {self.expressions}"
            )
            assert not self.empty(), "Cannot unwrap empty TypeUnion"

            cexpr = self.expressions[0]
        else:
            assert choice in self.sorts, f"Expected {choice} to be in {self.sorts}"
            choices = []
            for cexpr in self.expressions:
                if cexpr.expr.sort() == choice:
                    if constraint is not None:
                        if z3.eq(constraint, cexpr.constraint()):
                            choices.append(cexpr)
                    else:
                        choices.append(cexpr)
            assert (
                len(choices) == 1
            ), f"Found {len(choices)} expressions of sort {choice}; need one to unwrap."
            cexpr = choices[0]

        if constraint is None:
            assert (
                not cexpr.constrained()
            ), f"Expression {cexpr} has a constraint; cannot unwrap"
        else:
            assert (
                cexpr.constrained()
            ), f"Expected {cexpr} to have constraint {constraint}, not none"
            assert z3.eq(
                constraint, cexpr.constraint()
            ), f"Expression {cexpr} does not have expected constraint {constraint}"
        return cexpr.expr

    def map(self, oper: Callable[[Expression], Optional[Expression]]) -> TypeUnion:
        expressions = []
        sorts: SortSet = set()
        for cexpr in self.expressions:
            res = oper(cexpr.expr)
            if res is not None:
                cres = CExpr(expr=res, constraints=cexpr.constraints)
                expressions.append(cres)
                sorts.add(res.sort())
        return TypeUnion(expressions, sorts)
