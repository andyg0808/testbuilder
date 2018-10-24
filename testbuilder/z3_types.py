from __future__ import annotations

import inspect
from dataclasses import dataclass, field
from itertools import product
from typing import (
    Any as PyAny,
    Callable,
    Generic,
    List,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Type,
    TypeVar,
    Union,
    cast,
)

import z3
from logbook import Logger
from toolz import concat
from typeassert import assertify
from z3 import DatatypeRef

log = Logger("z3_types")

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
        return expr != z3.IntVal(0)
    elif z3.is_bool(expr):
        return cast(z3.Bool, expr)
    elif z3.is_string(expr):
        return z3.Length(cast(z3.String, expr)) != z3.IntVal(0)
    else:
        raise UnknownConversionException(
            f"Can't convert {expr.sort().name()} to boolean"
        )


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
        return bool_and(*(constraint for name, sort, constraint in self.constraints))

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
            return bool_and(cast(z3.Bool, expr), self.constraint())
        else:
            return expr


CExpr = ConstrainedExpression


ExpressionMap = MMapping[z3.SortRef, List[CExpr]]

SortSet = Set[z3.SortRef]


@dataclass(frozen=True)
class TypeUnion:
    expressions: List[CExpr[Expression]]
    sorts: SortSet

    @staticmethod
    def wrap(expr: Expression) -> TypeUnion:
        cexpr = CExpr(expr=expr)
        return TypeUnion([cexpr], {expr.sort()})

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
        return bool_or(boolexprs)

    def implications(self) -> z3.Bool:
        constraints = [
            cast(z3.Bool, x.constraint) for x in self.expressions if x.constrained()
        ]
        return bool_or(constraints)

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
        sorts = set()
        for cexpr in self.expressions:
            res = oper(cexpr.expr)
            if res is not None:
                cres = CExpr(expr=res, constraints=cexpr.constraints)
                expressions.append(cres)
                sorts.add(res.sort())
        return TypeUnion(expressions, sorts)


@dataclass(frozen=True)
class VariableTypeUnion(TypeUnion):
    name: str
    registrar: TypeRegistrar

    def _get_any(self) -> AnyT:
        return make_any(self.name)

    def expand(self) -> TypeUnion:
        return self.registrar.expand(self.name, self.sorts)

    def unwrap(self, *args: Any) -> Expression:
        """
        Tries to unwrap directly; if that fails, expands, then unwraps.
        """
        try:
            return super().unwrap(*args)
        except AssertionError:
            return self.expand().unwrap(*args)


@dataclass
class TypeRegistrar:
    anytype: AnySort

    @assertify
    def AllTypes(self, name: str, restricted: SortSet = set()) -> VariableTypeUnion:
        """
        Args:
            name: The variable name to create
            restricted: If non-empty, the name will be treated as
                already restricted to this set of sorts. If there is only
                one sort in the set, the name will be treated as always
                having that sort. If empty, the name will be
                unrestricted, as with expand.
        """
        if len(restricted) > 0:
            union = self.expand(name)
            sorts = {
                e.expr.sort() for e in union.expressions if e.expr.sort() in restricted
            }

            print(f"Restricting new VariableAnyType for {name} to sorts: {sorts}")
            return VariableTypeUnion(
                expressions=[], sorts=sorts, name=name, registrar=self
            )
        else:
            expr = make_any(name)
            return VariableTypeUnion(
                expressions=[], sorts=set(), name=name, registrar=self
            )

    def expand(self, name: str, types: Set[z3.SortRef] = set()) -> TypeUnion:
        """
        Arguments:
            name: The variable name to expand
            types: A set of sorts to restrict the variable to. If the
                set is empty, does not restrict the variable at all.
        """
        var = make_any(name)
        exprs = []
        sorts: Set[z3.SortRef] = set()
        for i in range(self.anytype.num_constructors()):
            expr = self.anytype.accessor(i, 0)(var)
            # Allow restricting the expansion of the variable
            if len(types) > 0:
                if expr.sort() not in types:
                    continue
            if len(types) == 1:
                cexpr = CExpr(expr=expr)
            else:
                constraint = self.anytype.recognizer(i)(var)
                constraints = [(name, expr.sort(), constraint)]
                cexpr = CExpr(expr=expr, constraints=constraints)
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
        if isinstance(value, VariableTypeUnion):
            # Special-case for TypeUnions which are already Any variables
            return TypeUnion.wrap(target == value._get_any())
        exprs = []
        for expr in value.expressions:
            assign = target == self.wrap(expr.expr)
            if expr.constrained():
                exprs.append(bool_and(assign, expr.constraint()))
            else:
                exprs.append(assign)

        return TypeUnion.wrap(bool_or(exprs))

    def to_boolean(self, value: TypeUnion, invert: bool = False) -> TypeUnion:
        """
        Convert all the expressions in this TypeUnion to booleans,
        applying truthy standards as needed in order to convert
        non-boolean types.
        """
        bools: List[CExpr[Expression]] = []
        for cexpr in value.expressions:
            expr = to_boolean(cexpr.expr)
            if invert:
                expr = bool_not(expr)
            bools.append(CExpr(expr=expr, constraints=cexpr.constraints))
        if len(bools) == 0 and isinstance(value, VariableTypeUnion):
            return self.to_boolean(value.expand(), invert)
        return TypeUnion(expressions=bools, sorts={z3.BoolSort()})


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
    """
    Function overloading and abstract type handling.

    A `MoreMagic` is a callable object which accepts any number of
    `TypeUnion`s as arguments. It searches for registered handler
    functions for each element of the Cartesian product of all the
    expressions in each `TypeUnion`. It discards those n-tuples of
    types which do not have defined handlers. For those which do have
    handlers, it calls the handler with the expressions from the
    n-tuple.

    """

    def __init__(self) -> None:
        self.funcref: MMapping[MoreMagicTag, MoreMagicFunc] = {}
        for _, method in inspect.getmembers(self, inspect.ismethod):
            magic = getattr(method, "__magic", None)
            if magic is not None:
                self.funcref[magic] = method

    @staticmethod
    def m(*types: Union[z3.SortRef, Type]) -> Callable[[MoreMagicFunc], MoreMagicFunc]:
        """
        Creates an instance of MoreMagic and calls `magic` on it with
        its arguments.
        """
        res = MoreMagic()
        return res.magic(*types)

    def magic(
        self, *types: Union[z3.SortRef, Type]
    ) -> Callable[[MoreMagicFunc], MoreMagic]:
        """
        To register an existing function for some argument types, call
        this method, passing it the argument types, and pass the
        existing function to the returned registration function. The
        registration function returns the original MoreMagic object,
        so calls can be chained.

        Arguments:
            *types: The argument types for which some function should be run_func
        Returns:
            A function to be passed a Callable to register for the
            argument types passed to `magic`.
        """

        def _magic(func: MoreMagicFunc) -> MoreMagic:
            self.funcref[tuple(types)] = func
            return self

        return _magic

    def __call__(self, *args: TypeUnion) -> TypeUnion:
        """
        Call this MoreMagic on the arguments. This will call the
        registered handler function (if it exists) for each element of
        the Cartesian product of expressions in the TypeUnions. The
        return values from the handlers which are called will be added
        to the resulting `TypeUnion`. n-tuples of the Cartesian
        product for which handlers do not exist will be skipped.
        """
        log.info(f"Called {self.__class__} on {args}")
        functions = []
        for arg_tuple in product(*(arg.expressions for arg in args)):
            func = self.__select(tuple(arg.expr.sort() for arg in arg_tuple))
            if func is None:
                continue
            functions.append((func, arg_tuple))
        exprs = []
        sorts = set()
        for func, args in functions:
            res = self.__call_on_exprs(func, args)
            if res is None:
                continue
            exprs.append(res)
            sorts.add(res.expr.sort())
        if len(exprs) == 0 and any(isinstance(arg, VariableTypeUnion) for arg in args):
            newargs = []
            for arg in args:
                if isinstance(arg, VariableTypeUnion):
                    newargs.append(arg.expand())
                else:
                    newargs.append(arg)
            return self(*newargs)
        return TypeUnion(exprs, sorts)

    def __call_on_exprs(
        self, func: Callable[..., Expression], args: Tuple
    ) -> Optional[CExpr]:
        log.info(f"Trying to run implementation for type-pair {args}")

        try:
            res = func(*(arg.expr for arg in args))
        except Exception as e:
            raise RuntimeError(
                f"Problem running {func}({', '.join(str(a) for a in args)})"
            ) from e
        constraints = list(concat(arg.constraints for arg in args))
        if len(constraints) > 0:
            return CExpr(expr=res, constraints=constraints)
        else:
            return CExpr(expr=res)

    def __select(self, args: Tuple) -> Optional[Callable[..., Expression]]:
        log.info(f"Selecting implementation using {args}")

        def sort_compare(arg_sort: z3.SortRef, func_key: z3.SortRef) -> bool:
            if isinstance(func_key, z3.SortRef):
                return func_key == arg_sort or func_key.subsort(arg_sort)
            elif isinstance(func_key, type):
                return isinstance(arg_sort, func_key)

        for key, func in self.funcref.items():
            log.info(f"Checking {key} against {args}")
            if all(sort_compare(*tu) for tu in zip(args, key)):
                return func
        return None


def bool_not(expr: z3.Bool) -> z3.Bool:
    return z3.Not(expr)


def bool_or(exprs: Sequence[z3.Bool]) -> z3.Bool:
    return _simplify_logical(exprs, z3.Or)


def bool_and(*exprs: z3.Bool) -> z3.Bool:
    return _simplify_logical(exprs, z3.And)


def _simplify_logical(
    exprs: Sequence[z3.Bool], function: Callable[..., z3.Bool]
) -> z3.Bool:
    if len(exprs) > 1:
        return function(*exprs)
    elif len(exprs) == 1:
        return exprs[0]
    else:
        raise RuntimeError("Need at least one expression to combine")


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
