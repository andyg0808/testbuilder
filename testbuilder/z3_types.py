from __future__ import annotations

from enum import Enum
from typing import Callable, Iterable, List, NewType, Optional, Set, Tuple, Union, cast

import z3

Expression = z3.ExprRef


class ReferenceT(z3.DatatypeRef):
    ...


class ReferenceSort(z3.DatatypeSortRef):
    def Reference(self, r: z3.Int) -> ReferenceT:
        ...


def make_ref_type() -> ReferenceSort:
    reference = z3.Datatype("Reference")
    reference.declare("Reference", ("r", z3.IntSort()))
    return cast(ReferenceSort, reference.create())


Reference: ReferenceSort = make_ref_type()


# class NilT(z3.ExprRef):
#     ...


# class NilSortT(z3.SortRef):
#     ...


# def make_nil_type() -> NilSortT:
#     nil = z3.DeclareSort("Nil")
#     return cast(NilSortT, z3.Const("nil", nil))


# NilSort: NilSortT = z3.DeclareSort("Nil")
# Nil: NilT = make_nil_type()


class AnyT(z3.DatatypeRef):
    ...


class PairT(z3.DatatypeRef):
    ...


class AnySort(z3.DatatypeSortRef):
    def Int(self, i: z3.Int) -> AnyT:
        ...

    def i(self, v: AnyT) -> z3.Int:
        ...

    def is_Int(self, v: Expression) -> z3.BoolRef:
        ...

    def Bool(self, i: z3.BoolRef) -> AnyT:
        ...

    def b(self, v: AnyT) -> z3.BoolRef:
        ...

    def is_Bool(self, v: Expression) -> z3.BoolRef:
        ...

    def s(self, v: AnyT) -> z3.String:
        ...

    def is_String(self, v: Expression) -> z3.BoolRef:
        ...


Sort = Enum("Sort", ["Reference"])


SortSet = Set[Union[z3.SortRef, Sort]]


def bool_not(expr: z3.BoolRef) -> z3.BoolRef:
    if z3.eq(expr, BOOL_TRUE):
        return BOOL_FALSE
    if z3.eq(expr, BOOL_FALSE):
        return BOOL_TRUE
    return z3.Not(expr)


def bool_or(exprs: Iterable[z3.BoolRef]) -> z3.BoolRef:
    return _simplify_logical(exprs, False, z3.Or)


def bool_and(exprs: Iterable[z3.BoolRef]) -> z3.BoolRef:
    return _simplify_logical(exprs, True, z3.And)


def bool_all(exprs: Iterable[z3.BoolRef]) -> z3.BoolRef:
    return bool_and(exprs)


def bool_any(exprs: Iterable[z3.BoolRef]) -> z3.BoolRef:
    """
    Allow any path in exprs to be taken. If only one path is present,
    it is required. No exprs results in an exception.
    """
    return bool_or(exprs)


BOOL_TRUE = z3.BoolVal(True)
BOOL_FALSE = z3.BoolVal(False)


def bool_true() -> z3.BoolRef:
    return BOOL_TRUE


def _simplify_logical(
    exprs: Iterable[z3.BoolRef], identity: bool, function: Callable[..., z3.BoolRef]
) -> z3.BoolRef:
    """
    Args:
        exprs: A list of boolean values to combine with `function`
        eliminate: The identity element of `function`. Removing this
                   value from exprs will not change the result of
                   `function` on the remaining values.
        function: The function to combine the elements of `exprs`
                  with. Expected to take a variable number of
                  arguments, as `exprs` will be splatted into it.
    """
    expr_list: List[z3.BoolRef] = list(exprs)
    if len(expr_list) == 0:
        raise RuntimeError("Need at least one expression to combine")
    # `eliminate_bool` is the value which, if present in expr_list, would
    # make the entire expression evaluate to itself. For `and`, this
    # is `False`; for `or`, this is `True`.
    eliminate_bool = z3.BoolVal(not identity)
    # Similarly to `eliminate_bool`, `identity_bool` is the value
    # which, if all the elements of `expr_list` are it, would make the
    # whole expression equal to itself. For `and`, this is `True`; for
    # `or`, this is `False`. Note that, if not every value in `expr_list`
    # is this value, any occurances of it can simply be deleted
    # without changing the value of the expression.
    identity_bool = z3.BoolVal(identity)

    # Flatten any child functions which are the same type as this one
    # into this one (i.e., `And(And(...), ...)` should become
    # `And(...)`).

    # This is hacky, but there doesn't seem to be a better way to get
    # the decl of `function`, because it's an actual Python function.
    decl = function().decl()

    new_exprs: List[z3.BoolRef] = []
    for expr in expr_list:
        if expr.decl() == decl:
            # This cast is safe because we know `function` operates
            # only on boolean values, so if `expr` has the `decl` of
            # `function`, it must also only operate on boolean values.
            new_exprs += cast(List[z3.BoolRef], expr.children())
        else:
            new_exprs.append(expr)
    expr_list = new_exprs

    # Resolve constants statically (e.g., in `And`, if all arguments
    # are statically `True`, return `True`, and if a `False` is
    # present as any argument, return `False`, since `And(False, ...)`
    # is always `False`.)
    if any(z3.eq(eliminate_bool, e) for e in expr_list):
        return eliminate_bool
    if all(z3.eq(identity_bool, e) for e in expr_list):
        return identity_bool

    # Remove static occurances of the identity element, since they do
    # not affect the outcome of the function.
    expr_list = [e for e in expr_list if not z3.eq(identity_bool, e)]

    # Strip operations with only one remaining argument.
    if len(expr_list) > 1:
        return function(*expr_list)
    else:
        return expr_list[0]


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
