from __future__ import annotations

from typing import (
    Callable,
    Generic,
    Iterable,
    List,
    MutableMapping as MMapping,
    Optional,
    Set,
    Tuple,
    TypeVar,
    cast,
)

from logbook import Logger

import z3
from dataclasses import dataclass, field

log = Logger("z3_types")

Expression = z3.ExprRef


class AnyT(z3.DatatypeRef):
    ...


class AnySort(z3.DatatypeSortRef):
    def none(self) -> AnyT:
        ...

    def is_none(self, v: Expression) -> z3.Bool:
        ...

    def Int(self, i: z3.Int) -> AnyT:
        ...

    def i(self, v: AnyT) -> z3.Int:
        ...

    def is_Int(self, v: Expression) -> z3.Bool:
        ...

    def Bool(self, i: z3.Bool) -> AnyT:
        ...

    def b(self, v: AnyT) -> z3.Bool:
        ...

    def is_Bool(self, v: Expression) -> z3.Bool:
        ...

    def s(self, v: AnyT) -> z3.String:
        ...

    def is_String(self, v: Expression) -> z3.Bool:
        ...


class UnknownConversionException(RuntimeError):
    pass


E = TypeVar("E", bound=Expression)

VarConstraint = Tuple[str, z3.SortRef, z3.Bool]


@dataclass
class ConstrainedExpression(Generic[E]):
    expr: E
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


CExpr = ConstrainedExpression


ExpressionMap = MMapping[z3.SortRef, List[CExpr]]

SortSet = Set[z3.SortRef]


def bool_not(expr: z3.Bool) -> z3.Bool:
    if z3.eq(expr, BOOL_TRUE):
        return BOOL_FALSE
    if z3.eq(expr, BOOL_FALSE):
        return BOOL_TRUE
    return z3.Not(expr)


def bool_or(exprs: Iterable[z3.Bool]) -> z3.Bool:
    return _simplify_logical(exprs, True, z3.Or)


def bool_and(exprs: Iterable[z3.Bool]) -> z3.Bool:
    return _simplify_logical(exprs, False, z3.And)


def bool_all(exprs: Iterable[z3.Bool]) -> z3.Bool:
    return bool_and(exprs)


def bool_any(exprs: Iterable[z3.Bool]) -> z3.Bool:
    """
    Allow any path in exprs to be taken. If only one path is present,
    it is required. No exprs results in an exception.
    """
    return bool_or(exprs)


BOOL_TRUE = z3.BoolVal(True)
BOOL_FALSE = z3.BoolVal(False)


def bool_true() -> Expression:
    return BOOL_TRUE


def _simplify_logical(
    exprs: Iterable[z3.Bool], eliminate: bool, function: Callable[..., z3.Bool]
) -> z3.Bool:
    exprs = list(exprs)
    if len(exprs) == 0:
        raise RuntimeError("Need at least one expression to combine")
    # `eliminate_bool` is the value which, if present in exprs, would
    # make the entire expression evaluate to itself. For `and`, this
    # is `False`; for `or`, this is `True`.
    eliminate_bool = z3.BoolVal(eliminate)
    # Similarly to `eliminate_bool`, `combine_bool` is the value
    # which, if all the elements of `exprs` are it, would make the
    # whole expression equal to itself. For `and`, this is `True`; for
    # `or`, this is `False`. Note that, if not every value in `exprs`
    # is this value, any occurances of it can simply be deleted
    # without changing the value of the expression.
    combine_bool = z3.BoolVal(not eliminate)
    if any(z3.eq(eliminate_bool, e) for e in exprs):
        return eliminate_bool
    if all(z3.eq(combine_bool, e) for e in exprs):
        return combine_bool
    exprs = [e for e in exprs if not z3.eq(combine_bool, e)]
    if len(exprs) > 1:
        return function(*exprs)
    else:
        return exprs[0]


def diff_expression(
    left: Expression, right: Expression
) -> Optional[List[Tuple[Expression, Expression]]]:
    """
    Returns the portion of an expression which is different between
    `left` and `right`. Returns `None` if `left` and `right` are
    `z3.eq`.
    """
    if z3.eq(left, right):
        return None

    if left.num_args() != right.num_args() or left.num_args() == 0:
        return [(left, right)]

    for l, r in zip(left.children(), right.children()):
        diff = diff_expression(l, r)
        if diff is not None:
            return [(left, right)] + diff
    raise RuntimeError(
        f"Could not find difference between dissimilar values {left} and {right}"
    )


def print_diff(diff: List[Tuple[Expression, Expression]]) -> None:
    for left, right in diff:
        print(f"Difference in\n\n{left}\n{right}\n")
