from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any as PyAny,
    Callable,
    Generator,
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

import z3
from logbook import Logger
from typeassert import assertify
from z3 import DatatypeRef

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
        return self.registrar.make_any(self.name)

    def expand(self) -> TypeUnion:
        return self.registrar.expand(self.name, self.sorts)

    def unwrap(self, *args: PyAny) -> Expression:
        """
        Tries to unwrap directly; if that fails, expands, then unwraps.
        """
        try:
            return super().unwrap(*args)
        except AssertionError:
            return self.expand().unwrap(*args)


class TypeBuilder:
    any_index = 0

    def __init__(self, name_part: str = "") -> None:
        TypeBuilder.any_index += 1
        self.index = TypeBuilder.any_index
        print(f"Starting new TypeBuilder with index {self.index}")
        if name_part:
            self.datatype = z3.Datatype(f"{name_part}_{self.index}")
        else:
            self.datatype = z3.Datatype(f"Any_{self.index}")

    def wrappers(self) -> TypeBuilder:
        self.datatype.declare("Int", ("i", z3.IntSort()))
        self.datatype.declare("Bool", ("b", z3.BoolSort()))
        self.datatype.declare("String", ("s", z3.StringSort()))
        return self

    def none(self) -> TypeBuilder:
        self.datatype.declare("none")
        return self

    def structures(self) -> TypeBuilder:
        self.datatype.declare(
            "Pair", ("Pair_left", self.datatype), ("Pair_right", self.datatype)
        )
        return self

    def build(self) -> TypeRegistrar:
        return TypeRegistrar(cast(AnySort, self.datatype.create()))

    def construct(self) -> TypeRegistrar:
        self.none()
        self.wrappers()
        self.structures()
        return self.build()


@dataclass
class TypeRegistrar:
    anytype: AnySort

    def constructors(self) -> Generator[z3.FuncDeclRef, None, None]:
        for i in range(self.anytype.num_constructors()):
            yield self.anytype.constructor(i)

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
        else:
            sorts = set()
        return VariableTypeUnion(expressions=[], sorts=sorts, name=name, registrar=self)

    def make_any(self, name: str) -> AnyT:
        return cast(AnyT, z3.Const(name, self.anytype))

    def expand(self, name: str, types: Set[z3.SortRef] = set()) -> TypeUnion:
        """
        Arguments:
            name: The variable name to expand
            types: A set of sorts to restrict the variable to. If the
                set is empty, does not restrict the variable at all.
        """
        var = self.make_any(name)
        exprs = []
        sorts: Set[z3.SortRef] = set()
        for i in range(self.anytype.num_constructors()):
            constructor = self.anytype.constructor(i)
            if constructor.arity() == 1:
                expr = self.anytype.accessor(i, 0)(var)
            else:
                expr = var
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
            if val.decl() == self.anytype.i:
                return val.arg(0)  # type: ignore
            return self.anytype.Int(val)  # type: ignore
        if val.sort() == z3.StringSort():
            if val.decl() == self.anytype.s:
                return val.arg(0)  # type: ignore
            return self.anytype.String(val)  # type: ignore
        if val.sort() == z3.BoolSort():
            if val.decl() == self.anytype.b:
                return val.arg(0)  # type: ignore
            return self.anytype.Bool(val)  # type: ignore
        if val.sort() == self.anytype:
            # This can happen if we already have a wrapped type, or if
            # the type is a non-wrapper type
            return val  # type: ignore
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
                exprs.append(bool_and([assign, expr.constraint()]))
            else:
                exprs.append(assign)

        return TypeUnion.wrap(bool_or(exprs))

    def to_boolean(self, value: TypeUnion, invert: bool = False) -> TypeUnion:
        """
        Convert all the expressions in this TypeUnion to booleans,
        applying truthy standards as needed in order to convert
        non-boolean types.
        """
        if isinstance(value, VariableTypeUnion):
            # Always want to work on expanded version, because a
            # VariableTypeUnion is either unconstrained or empty. If
            # unconstrained, we need to expand to get constrained
            # values. If empty, expanding gets the appropriate
            # constrained values.
            return self.to_boolean(value.expand(), invert)
        bools: List[CExpr[Expression]] = []
        for cexpr in value.expressions:
            expr = self.expr_to_boolean(cexpr.expr)
            if invert:
                expr = bool_not(expr)
            bools.append(CExpr(expr=expr, constraints=cexpr.constraints))
        return TypeUnion(expressions=bools, sorts={z3.BoolSort()})

    def expr_to_boolean(self, expr: Expression) -> z3.Bool:
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
        elif expr.sort() == self.anytype:
            if hasattr(self.anytype, "none") and expr.decl() == self.anytype.none:
                return z3.BoolVal(False)
            else:
                # For all anytype values that aren't None, assume they
                # are true. This will not be the case for some types,
                # but it's true for our current set of types
                return z3.BoolVal(True)
        else:
            raise UnknownConversionException(
                f"Can't convert {expr.sort().name()} to boolean"
            )

    def unwrap(self, val: Expression) -> Expression:
        """
        Extracts a value from an Any type.

        Assumes all constructors for Any take a single argument, which is the
        value stored in them.
        """
        if val.sort() == self.anytype:
            if val.num_args() == 1:
                return val.arg(0)
        return val


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
