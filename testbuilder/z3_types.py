from __future__ import annotations

import inspect
from dataclasses import dataclass
from itertools import product
from typing import (
    Any as PyAny,
    Callable,
    Generic,
    List,
    MutableMapping as MMapping,
    Optional,
    Set,
    Tuple,
    Type,
    TypeVar,
    Union,
    cast,
)

import z3
from typeassert import assertify
from z3 import DatatypeRef

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

    def s(self, v: AnyT) -> z3.String:
        ...

    def is_String(self, v: Expression) -> z3.Bool:
        ...


AnyDatatype = z3.Datatype("Any")
AnyDatatype.declare("Int", ("i", z3.IntSort()))
AnyDatatype.declare("Bool", ("b", z3.BoolSort()))
AnyDatatype.declare("String", ("s", z3.StringSort()))
Any: AnySort = cast(AnySort, AnyDatatype.create())

T = TypeVar("T")


def to_boolean(expr: Expression) -> z3.Bool:
    """
    Apply Python's truthy standards to make a boolean of an
    expression.
    """
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


E = TypeVar("E", bound=Expression)


@dataclass
class ConstrainedExpression(Generic[E]):
    expr: E
    constraint: Optional[z3.Bool] = None

    def constrained(self) -> bool:
        return self.constraint is not None

    def to_expr(self, invert: bool = False) -> Expression:
        expr = cast(z3.Bool, self.expr)
        if invert:
            expr = bool_not(expr)
        if self.constraint is not None:
            assert self.expr.sort() == z3.BoolSort(), (
                "Cannot to_expr a ConstrainedExpression with constraints"
                " which doesn't have a boolean expr"
            )
            return bool_and(expr, self.constraint)
        else:
            return expr


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

    def to_expr(self, invert: bool = False) -> z3.Bool:
        """
        Creates a boolean expression allowing execution to procede down
        any of the possible expressions in this TypeUnion
        """
        assert (
            self.is_bool()
        ), "Cannot convert non-boolean TypeUnion to boolean expression"
        boolexprs: List[z3.Bool] = [
            cast(z3.Bool, x.to_expr(invert)) for x in self.expressions
        ]
        return bool_or(*boolexprs)

    def implications(self) -> z3.Bool:
        return bool_or(*(x.constraint for x in self.expressions if x.constrained()))

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
            assert len(self.expressions) < 2, (
                "Cannot unwrap TypeUnion without exactly one "
                f"value; this has {self.expressions}"
            )
            assert len(self.expressions) > 0, "Cannot unwrap empty TypeUnion"

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
            assert (
                cexpr.constraint is not None
            ), f"Expected {cexpr} to have constraint {constraint}, not none"
            assert z3.eq(
                constraint, cexpr.constraint
            ), f"Expression {cexpr} does not have expected constraint {constraint}"
        return cexpr.expr

    def map(self, oper: Callable[[Expression], Optional[Expression]]) -> TypeUnion:
        expressions = []
        sorts = set()
        for cexpr in self.expressions:
            res = oper(cexpr.expr)
            if res is not None:
                cres = CExpr(expr=res, constraint=cexpr.constraint)
                expressions.append(cres)
                sorts.add(res.sort())
        return TypeUnion(expressions, sorts)


@dataclass(frozen=True)
class AnyTypeUnion(TypeUnion):
    registrar: TypeRegistrar

    def _get_any(self) -> AnyT:
        def getatr(name: str) -> PyAny:
            return object.__getattribute__(self, name)

        assert getatr("sorts") == {Any}
        assert len(getatr("expressions")) == 1
        cexpr = getatr("expressions")[0]
        assert cexpr.constraint is None
        expr = cexpr.expr
        assert expr.sort() == Any
        return cast(AnyT, expr)

    def expand(self) -> TypeUnion:
        def getatr(name: str) -> PyAny:
            return object.__getattribute__(self, name)

        expr = getatr("_get_any")()
        name = expr.decl().name()
        return cast(TypeUnion, getatr("registrar").expand(name))

    def __getattribute__(self, name: str) -> PyAny:
        if name.startswith("_") or name == "registrar":
            return object.__getattribute__(self, name)
        expanded = object.__getattribute__(self, "expand")()
        print("Getting", name, "on", expanded)
        return getattr(expanded, name)


@dataclass
class TypeRegistrar:
    anytype: AnySort

    def AllTypes(self, name: str) -> AnyTypeUnion:
        expr = make_any(name)
        return AnyTypeUnion(expressions=[CExpr(expr=expr)], sorts={Any}, registrar=self)

    def expand(self, name: str) -> TypeUnion:
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

    def wrap(self, val: Expression) -> AnyT:
        if val.sort() == z3.IntSort():
            return self.anytype.Int(val)  # type: ignore
        if val.sort() == z3.StringSort():
            return self.anytype.String(val)  # type: ignore
        if val.sort() == z3.BoolSort():
            return self.anytype.Bool(val)  # type: ignore
        raise RuntimeError("Unknown type being wrapped")

    @assertify
    def assign(self, target: DatatypeRef, value: TypeUnion) -> TypeUnion:
        if isinstance(value, AnyTypeUnion):
            # Special-case for TypeUnions which are just unconstrained variables
            return TypeUnion.wrap(target == value._get_any())
        exprs = []
        for expr in value.expressions:
            assign = target == self.wrap(expr.expr)
            if expr.constraint is not None:
                exprs.append(bool_and(assign, expr.constraint))
            else:
                exprs.append(assign)

        return TypeUnion.wrap(bool_or(*exprs))

    def to_boolean(self, value: TypeUnion) -> TypeUnion:
        """
        Convert all the expressions in this TypeUnion to booleans,
        applying truthy standards as needed in order to convert
        non-boolean types.
        """
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
        if val.num_args() == 1:
            return val.arg(0)
        else:
            raise RuntimeError("Unexpected constructor for unwrapping")
    return val


MoreMagicFunc = Callable[..., T]


def more_magic_tag(*types: z3.SortRef) -> Callable[[MoreMagicFunc], MoreMagicFunc]:
    def _magic(func: MoreMagicFunc) -> MoreMagicFunc:
        setattr(func, "__magic", tuple(types))
        return func

    return _magic


MoreMagicTag = Tuple


class MoreMagic:
    def __init__(self) -> None:
        self.funcref: MMapping[MoreMagicTag, MoreMagicFunc] = {}
        for _, method in inspect.getmembers(self, inspect.ismethod):
            magic = getattr(method, "__magic", None)
            if magic is not None:
                self.funcref[magic] = method

    @staticmethod
    def m(*types: Union[z3.SortRef, Type]) -> Callable[[MoreMagicFunc], MoreMagicFunc]:
        res = MoreMagic()
        return res.magic(*types)

    def magic(
        self, *types: Union[z3.SortRef, Type]
    ) -> Callable[[MoreMagicFunc], MoreMagic]:
        def _magic(func: MoreMagicFunc) -> MoreMagic:
            self.funcref[tuple(types)] = func
            return self

        return _magic

    def __call__(self, *args: TypeUnion) -> TypeUnion:
        print(f"Called {self.__class__} on {args}")
        exprs = []
        sorts = set()
        for arg_tuple in product(*(arg.expressions for arg in args)):
            res = self.__call_on_exprs(arg_tuple)
            if res is None:
                continue
            exprs.append(res)
            sorts.add(res.expr.sort())
        if len(exprs) == 0 and any(isinstance(arg, AnyTypeUnion) for arg in args):
            newargs = []
            for arg in args:
                if isinstance(arg, AnyTypeUnion):
                    newargs.append(arg.expand())
                else:
                    newargs.append(arg)
                self(*newargs)
        return TypeUnion(exprs, sorts)

    def __call_on_exprs(self, args: Tuple) -> Optional[CExpr]:
        print(f"calling {args}")
        func = self.__select(tuple(arg.expr.sort() for arg in args))
        if func is None:
            return None
        res = func(*(arg.expr for arg in args))
        constraints = [arg.constraint for arg in args if arg.constraint is not None]
        if len(constraints) > 0:
            return CExpr(expr=res, constraint=bool_and(*constraints))
        else:
            return CExpr(expr=res)

    def __select(
        self, args: Tuple
    ) -> Optional[Callable[[Expression, Expression], Expression]]:
        print(f"selecting using {args}")

        def sort_compare(arg_sort: z3.SortRef, func_key: z3.SortRef) -> bool:
            if isinstance(func_key, z3.SortRef):
                return func_key == arg_sort or func_key.subsort(arg_sort)
            elif isinstance(func_key, type):
                return isinstance(arg_sort, func_key)

        for key, func in self.funcref.items():
            print(f"Matching {key} {args}")
            if all(sort_compare(*tu) for tu in zip(args, key)):
                return func
        return None


def bool_not(expr: z3.Bool) -> z3.Bool:
    return z3.Not(expr)


def bool_or(*exprs: z3.Bool) -> z3.Bool:
    return _simplify_logical(exprs, z3.Or)


def bool_and(*exprs: z3.Bool) -> z3.Bool:
    return _simplify_logical(exprs, z3.And)


def _simplify_logical(
    exprs: Tuple[z3.Bool, ...], function: Callable[..., z3.Bool]
) -> z3.Bool:
    if len(exprs) > 1:
        return function(*exprs)
    elif len(exprs) == 1:
        return exprs[0]
    else:
        raise RuntimeError("Need at least one expression to combine")
