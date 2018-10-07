from __future__ import annotations

import inspect
from dataclasses import dataclass, field
from functools import singledispatch
from itertools import groupby
from typing import (
    Set,
    Generic,
    Sequence,
    Iterator,
    cast,
    MutableMapping as MMapping,
    Optional,
    TypeVar,
    List,
    Callable,
    Tuple,
    Any as PyAny,
)
from .visitor import SimpleVisitor
from typeassert import assertify

import z3

Expression = z3.ExprRef


class AnyT(z3.DatatypeRef):
    ...


class AnySort(z3.DatatypeSortRef):
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


AnyDatatype = z3.Datatype("Any")
AnyDatatype.declare("Int", ("i", z3.IntSort()))
AnyDatatype.declare("Bool", ("b", z3.BoolSort()))
Any: AnySort = cast(AnySort, AnyDatatype.create())

T = TypeVar("T")


def to_boolean(expr: Expression) -> z3.Bool:
    if z3.is_int(expr):
        return expr == z3.IntVal(0)
    elif z3.is_bool(expr):
        return cast(z3.Bool, expr)
    else:
        raise UnknownConversionException(
            f"Can't convert {expr.sort().name()} to boolean"
        )


class UnknownConversionException(RuntimeError):
    pass


# ConstraintMap = MMapping[z3.SortRef, z3.Bool]
# ExpressionMap = MMapping[z3.SortRef, Expression]

E = TypeVar("E", bound=Expression)


@dataclass
class ConstrainedExpression(Generic[E]):
    expr: E
    constraint: Optional[z3.Bool]

    def constrained(self) -> bool:
        return self.constraint is not None

    def to_expr(self) -> Expression:
        if self.constraint is not None:
            assert self.expr.sort() == z3.BoolSort(), (
                "Cannot to_expr a ConstrainedExpression with constraints"
                " which doesn't have a boolean expr"
            )
            return bool_and(self.expr, self.constraint)
        else:
            return self.expr


CExpr = ConstrainedExpression


ExpressionMap = MMapping[z3.SortRef, List[ConstrainedExpression]]

SortSet = Set[z3.SortRef]


@dataclass(frozen=True)
class TypeUnion:
    expressions: List[ConstrainedExpression[Expression]]
    sorts: SortSet

    @staticmethod
    def wrap(expr: Expression, constraint: Optional[z3.Bool] = None) -> TypeUnion:
        cexpr = CExpr(expr=expr, constraint=constraint)
        return TypeUnion([cexpr], {expr.sort()})

    @staticmethod
    def cwrap(expr: CExpr) -> TypeUnion:
        return TypeUnion([expr], {expr.expr.sort()})

    def is_bool(self) -> bool:
        return self.sorts == {z3.BoolSort()}

    def to_expr(self) -> z3.Bool:
        assert (
            self.is_bool()
        ), "Cannot convert non-boolean TypeUnion to boolean expression"
        boolexprs = [x.to_expr() for x in self.expressions]
        return bool_or(*boolexprs)

    def unwrap(
        self,
        choice: Optional[z3.SortRef] = None,
        constraint: Optional[Expression] = None,
    ) -> Expression:
        print("Choice", choice)
        if choice is None:
            assert (
                len(self.sorts) <= 1
            ), f"Cannot unwrap TypeUnion with more than one type; this has {self.sorts}"
            assert len(self.expressions) == 1, (
                f"Cannot unwrap TypeUnion without exactly one "
                "value; this has {self.expressions}"
            )

            cexpr = self.expressions[0]
        else:
            assert choice in self.sorts, f"Expected {choice} to be in {self.sorts}"
            choices = []
            for cexpr in self.expressions:
                if cexpr.expr.sort() == choice:
                    choices.append(cexpr)
            assert (
                len(choices) == 1
            ), f"Found {len(choices)} expressions of sort {choice}; need one to unwrap."
            cexpr = choices[0]

        if constraint is None:
            assert (
                cexpr.constraint is None
            ), f"Expression {cexpr} has a constraint; cannot unwrap"
        else:
            assert z3.eq(
                constraint, cexpr.constraint
            ), f"Expression {cexpr} does not have expected constraint {constraint}"
        return cexpr.expr

    # def unwrap(self) -> Expression:
    #     assert (
    #         len(self.expressions) == 1
    #     ), "Cannot unwrap TypeUnion with more than one type"
    #     for s, v in self.expressions.items():
    #         assert s not in self.constraints
    #         return v
    #     raise RuntimeError("Cannot unwrap empty TypeUnion")

    # def map(self, oper: Callable[[Expression, Optional[z3.Bool]], T]) -> Iterator[T]:
    #     def _map(pair: Tuple[z3.SortRef, Expression]) -> T:
    #         sort, expr = pair
    #         constraint = self.constraints.get(sort, None)
    #         return oper(expr, constraint)

    #     return map(_map, self.expressions.items())


# @dataclass
# class TypeUnion:
#     # Need to tie constraints directly to each possible value, in
#     # order to ensure multiple values which can generate the same type
#     # don't miss their needful constraints.
#     expressions: ExpressionMap
#     constraints: ConstraintMap = field(default_factory=dict)

#     def add(self, sort: z3.SortRef, expr: Expression) -> None:
#         self.expressions[sort] = expr

#     def get(self, sort: z3.SortRef) -> Optional[Expression]:
#         return self.expressions.get(sort, None)

#     def constrain(self, sort: z3.SortRef) -> z3.Bool:
#         if sort not in self.constraints:
#             raise TypeError(f"TypeUnion does not contain expected type {sort}")
#         return self.constraints[sort]

#     def is_bool(self) -> bool:
#         return self.expressions.keys() == {z3.BoolSort()}

#     def to_expr(self) -> z3.Bool:
#         bool_sort = z3.BoolSort()
#         assert (
#             self.is_bool()
#         ), "Cannot convert non-boolean TypeUnion to boolean expression"
#         value = self.expressions[bool_sort]
#         constraints = self.constraints.get(bool_sort, None)
#         if constraints:
#             return bool_and(value, constraints)
#         else:
#             return cast(z3.Bool, value)

#     def unwrap(self) -> Expression:
#         assert (
#             len(self.expressions) == 1
#         ), "Cannot unwrap TypeUnion with more than one type"
#         for s, v in self.expressions.items():
#             assert s not in self.constraints
#             return v
#         raise RuntimeError("Cannot unwrap empty TypeUnion")

#     def map(self, oper: Callable[[Expression, Optional[z3.Bool]], T]) -> Iterator[T]:
#         def _map(pair: Tuple[z3.SortRef, Expression]) -> T:
#             sort, expr = pair
#             constraint = self.constraints.get(sort, None)
#             return oper(expr, constraint)

#         return map(_map, self.expressions.items())

#     # def map(self, func: Callable[[Expression], Expression]) -> TypeUnion:
#     #     def keyfunc(p: Tuple[PyAny, Expression]) -> z3.SortRef:
#     #         return p[1].sort()

#     #     mapped = [
#     #         (self.constraints.get(s, None), func(v))
#     #         for s, v in self.expressions.items()
#     #     ]
#     #     mapped.sort(key=keyfunc)
#     #     groups = groupby(mapped, keyfunc)
#     #     expressions = {}
#     #     constraints: MMapping[z3.SortRef, z3.Bool] = {}
#     #     for sort, pairs in groups:
#     #         exprs = []
#     #         constrs: List[Expression] = []
#     #         for constr, expr in pairs:
#     #             if constr:
#     #                 constrs.append(constr)
#     #             exprs.append(expr)
#     #         expressions[sort] = bool_or(*exprs)
#     #         constraints[sort] = cast(z3.Bool, bool_or(*constrs))
#     #     return TypeUnion(expressions=expressions, constraints=constraints)

#     # def map_pair(self, other: TypeUnion, visitor: Callable[[T, T], Expression]) -> TypeUnion:
#     #     pairs = zip(self.expressions.values(), other.expressions.values())
#     #     result = groupby((visitor(l, r) for l, r in pairs),
#     #     groups =


@dataclass
class TypeRegistrar:
    anytype: AnySort

    def AllTypes(self, name: str) -> TypeUnion:
        var = make_any(name)
        exprs = []
        sorts: SortSet = set()
        for i in range(self.anytype.num_constructors()):
            constraint = self.anytype.recognizer(i)(var)
            expr = self.anytype.accessor(i, 0)(var)
            cexpr = CExpr(expr=expr, constraint=constraint)
            exprs.append(cexpr)
            sorts.add(expr.sort())
        return TypeUnion(exprs, sorts)

    # def union(self, expr: CExpr) -> TypeUnion:
    #     return TypeUnion([expr], {expr.expr.sort()})

    # def wrap(self, expr: Expression, constraint: Optional[z3.Bool] = None) -> TypeUnion:
    #     cexpr = CExpr(expr=expr, constraint=constraint)
    #     return TypeUnion([cexpr], expr.sort(): [cexpr]})

    # def Int(self, val: z3.Int, constraint: Optional[z3.Bool] = None) -> TypeUnion:
    #     cexpr = CExpr(expr=val, constraint=constraint)
    #     return self.union(val.sort(), [
    #     return TypeUnion({z3.IntSort(): [cexpr]})

    # def String(self, val: z3.String) -> TypeUnion:
    #     return TypeUnion({z3.StringSort(): val})

    # def Bool(self, val: z3.Bool) -> TypeUnion:
    #     return TypeUnion({z3.BoolSort(): val})

    def wrap(self, val: Expression) -> AnyT:
        if val.sort() == z3.IntSort():
            return self.anytype.Int(val)  # type: ignore
        if val.sort() == z3.StringSort():
            return self.anytype.String(val)  # type: ignore
        raise RuntimeError("Unknown type being wrapped")

    @assertify
    def assign(self, target: AnyT, value: TypeUnion) -> TypeUnion:
        exprs = []
        for expr in value.expressions:
            # constraints = value.constraints.get(sort, None)
            assign = target == self.wrap(expr.expr)
            if expr.constraint is not None:
                exprs.append(bool_and(assign, expr.constraint))
            else:
                exprs.append(assign)

        return TypeUnion.wrap(bool_or(*exprs))

    def to_boolean(self, value: TypeUnion) -> TypeUnion:
        bools: List[z3.Bool] = []
        for cexpr in value.expressions:
            if cexpr.constraint:
                bools.append(bool_and(to_boolean(cexpr.expr), cexpr.constraint))
            else:
                bools.append(to_boolean(cexpr.expr))
        return TypeUnion.wrap(bool_or(*bools))


def make_any(name: str) -> AnyT:
    return cast(AnyT, z3.Const(name, Any))


def unwrap(val: Expression) -> Expression:
    """
    Extracts a value from an Any type.

    Assumes all constructors for Any take a single argument, which is the
    value stored in them.
    """
    if val.sort() == Any:
        return val.arg(0)
    return val


MagicFunc = Callable[[E, E], Expression]
MagicTag = Tuple[z3.SortRef, z3.SortRef]


def magic_tag(left: z3.SortRef, right: z3.SortRef) -> Callable[[MagicFunc], MagicFunc]:
    def _magic(func: MagicFunc) -> MagicFunc:
        setattr(func, "__magic", (left, right))
        return func

    return _magic


class Magic:
    def __init__(self) -> None:
        self.funcref: MMapping[MagicTag, MagicFunc] = {}
        for _, method in inspect.getmembers(self, inspect.ismethod):
            magic = getattr(method, "__magic", None)
            if magic is not None:
                self.funcref[magic] = method

    def __call__(self, left: TypeUnion, right: TypeUnion) -> TypeUnion:
        exprs = []
        sorts = set()
        for lexpr in left.expressions:
            for rexpr in right.expressions:
                # Would need cartesian product of potential expressions
                # here; might want to do a couple assignments first.
                res = self.__call_on_exprs(lexpr, rexpr)
                if res is None:
                    continue
                exprs.append(res)
                sorts.add(res.expr.sort())
        return TypeUnion(exprs, sorts)

    def __call_on_exprs(self, left: CExpr, right: CExpr) -> CExpr:
        func = self.__select(left.expr.sort(), right.expr.sort())
        if func is None:
            return None
        res = func(left.expr, right.expr)
        constraints = []
        if left.constraint is not None:
            constraints.append(left.constraint)
        if right.constraint is not None:
            constraints.append(right.constraint)
        return CExpr(expr=res, constraint=bool_and(*constraints))

    def __select(
        self, lsort: z3.SortRef, rsort: z3.SortRef
    ) -> Optional[Callable[[Expression, Expression], Expression]]:
        return self.funcref.get((lsort, rsort), None)

    def addInt(self, left: z3.Int, right: z3.Int) -> z3.Int:
        pass

    def addString(self, left: z3.String, right: z3.String) -> z3.String:
        pass


def bool_not(expr: Expression) -> Expression:
    return z3.Not(expr)


def bool_or(*exprs: Expression) -> Expression:
    return _simplify_logical(exprs, z3.Or)


def bool_and(*exprs: Expression) -> Expression:
    return _simplify_logical(exprs, z3.And)


def _simplify_logical(
    exprs: Tuple[Expression, ...], function: Callable[..., Expression]
) -> Expression:
    if len(exprs) > 1:
        return function(*exprs)
    else:
        return exprs[0]
