"""
Converts an expression from Python AST into a z3 expression. The
structural aspects of converting Python are handled by the code in
`ssa_to_expression`.
"""
from __future__ import annotations

import operator
import re
from functools import reduce
from typing import Any, Callable, List, Mapping, Optional, Sequence, cast

from logbook import Logger
from toolz import groupby, mapcat
from visitor import SimpleVisitor

import z3

from . import nodetree as n
from .constrained_expression import ConstrainedExpression as CExpr, ConstraintSet
from .expandable_type_union import ExpandableTypeUnion
from .expression_type_union import ExpressionTypeUnion
from .magic import Magic, MagicFountain, SortingFunc, magic_tag as magic
from .store import Store
from .type_manager import TypeManager
from .type_registrar import TypeRegistrar
from .type_union import TypeUnion
from .variable_type_union import VariableTypeUnion
from .z3_types import (
    BOOL_FALSE,
    BOOL_TRUE,
    Expression,
    GenerationError,
    Reference,
    ReferenceT,
    SortMarker,
    SortSet,
    bool_and,
    bool_or,
)

log = Logger("converter")

OpFunc = Callable[..., TypeUnion]
TypeRegex = re.compile(r"^(?:([A-Z])_)?(.+)$", re.IGNORECASE)
TypeConstructor = Callable[[str], Expression]


IntSort = z3.IntSort()
RealSort = z3.RealSort()
StringSort = z3.StringSort()
BoolSort = z3.BoolSort()
ArithSort = z3.ArithSortRef


class SortNamer:
    def __init__(self, anytype: z3.DatatypeSortRef) -> None:
        keys = ["Nil"]
        self.anytype = anytype
        self.values: List[z3.DatatypeRef] = []
        for key in keys:
            value = getattr(anytype, key, None)
            if value is not None:
                self.values.append(value)

    def __call__(self, expr: Expression) -> Optional[SortMarker]:
        sort = expr.sort()
        decl = expr.decl()
        if decl in self.values:
            return decl
        elif sort == self.anytype:
            return None
        else:
            return sort


class ExpressionConverter(SimpleVisitor[TypeUnion]):
    def __init__(
        self, registrar: TypeRegistrar, type_manager: TypeManager, store: Store
    ) -> None:
        super().__init__()
        self.registrar = registrar
        self.type_manager = type_manager
        self.store = store
        self.constants: Mapping[Any, TypeUnion] = {
            True: TypeUnion.wrap(z3.BoolVal(True)),
            False: TypeUnion.wrap(z3.BoolVal(False)),
        }
        nil = getattr(self.registrar.anytype, "Nil", None)
        if nil is not None:
            self.constants[None] = TypeUnion.wrap(nil)

        self.sorting = SortNamer(self.registrar.anytype)
        self.fount = MagicFountain(self.sorting)
        self.visit_oper = OperatorConverter(store, registrar, self.fount)
        self.builtins = {"len": self.fount(StringSort)(z3.Length)}

    def visit_Int(self, node: n.Int) -> TypeUnion:
        return TypeUnion.wrap(z3.IntVal(node.v))

    def visit_Float(self, node: n.Float) -> TypeUnion:
        return TypeUnion.wrap(z3.RealVal(node.v))

    def visit_Str(self, node: n.Str) -> TypeUnion:
        return TypeUnion.wrap(z3.StringVal(node.s))

    def visit_BinOp(self, node: n.BinOp) -> TypeUnion:
        op = self.visit_oper(node.op)
        expr = op(self.visit(node.left), self.visit(node.right))
        var_constraints: ConstraintSet = reduce(
            lambda c, e: c | e.constraints, expr.expressions, set()
        )
        var_updates = groupby(lambda c: c[0], var_constraints)
        for varname, constraints in var_updates.items():
            self.type_manager.put(
                varname, {c[1] for c in constraints if c[1] is not None}
            )
        return expr

    def visit_UnaryOp(self, node: n.UnaryOp) -> TypeUnion:
        op = self.visit_oper(node.op)
        return op(self.visit(node.operand))

    def visit_Return(self, node: n.Return) -> TypeUnion:
        if node.value:
            expr = self.visit(node.value)
            return self.registrar.assign(self.registrar.make_any("ret"), expr)
        else:
            return TypeUnion.wrap(z3.BoolVal(True))

    def visit_NameConstant(self, node: n.NameConstant) -> TypeUnion:
        return self.constants[node.value]

    def dereference(self, val: TypeUnion) -> TypeUnion:
        return self.fount(Reference)(self.store.get)(val)

    def visit_Attribute(self, node: n.Attribute) -> TypeUnion:
        value = self.visit(node.value)
        attr = node.attr
        if attr not in ["left", "right"]:
            raise GenerationError(
                f"Attribute {attr} not `left` or `right`; try rewriting it?"
            )
        assert (
            self.registrar.reftype is not None
        ), "Need reference types enabled to use attributes"

        if value.sorts == {self.registrar.anytype}:
            raise GenerationError(
                "Attempted to dereference None value. "
                "This may be caused by a function substitution "
                "which could never take a particular path"
            )

        accessor = getattr(self.registrar.reftype, "Pair_" + attr)

        dereferenced = self.dereference(value)
        component = self.fount(self.registrar.reftype)(accessor)(dereferenced)
        assert len(component.expressions) == 1
        return ExpressionTypeUnion(
            component.expressions, component.sorts, self.registrar
        )

    def visit_Name(self, node: n.Name) -> VariableTypeUnion:
        # TODO: Can any of this be replaced with make_any
        variable = get_variable(node.id, node.set_count)
        sorts = self.type_manager.get(variable)
        if sorts is not None:
            log.debug(f"Looked up {variable} and got sorts {sorts}")
            return self.registrar.AllTypes(variable, sorts)
        self.type_manager.put(variable)
        return self.registrar.AllTypes(variable)

    def visit_PrefixedName(self, node: n.PrefixedName) -> TypeUnion:
        variable = get_prefixed_variable(node)
        sorts = self.type_manager.get(variable)
        if sorts is not None:
            return self.registrar.AllTypes(variable, sorts)
        self.type_manager.put(variable)
        return self.registrar.AllTypes(variable)

    def visit_Result(self, node: n.Result) -> TypeUnion:
        variable = get_result(node)
        sorts = self.type_manager.get(variable)
        if sorts is not None:
            return self.registrar.AllTypes(variable, sorts)
        self.type_manager.put(variable)
        return self.registrar.AllTypes(variable)

    def visit_Set(self, node: n.Set) -> TypeUnion:
        log.debug("Visiting a set {}", node)
        value = self.visit(node.e)
        return self.assign(node.target, value)

    # Below is a potential solution to the problem of type
    # contradictions in substituted code. However, it makes the
    # simpler case much more messy, as the resulting expression will
    # need to handle every possible argument type, even those which
    # can statically be determined to be impossible. The best solution
    # would probably be to stop substituting functions and pass them
    # to Z3 as functions.

    # def visit_ArgumentBind(self, node: n.ArgumentBind) -> TypeUnion:
    #     log.debug("Visit argument binding {}", node)
    #     # if node.target.func == "insert":
    #     #     breakpoint()
    #     value = self.visit(node.e)
    #     return self.assign(node.target, value, typed=False)

    def visit_Assert(self, node: n.Assert) -> TypeUnion:
        expr = self.visit(node.test)
        return expr

    def visit_TupleVal(self, node: n.TupleVal) -> TypeUnion:
        log.warn("Skipping test case due to use of tuple")
        raise TupleError()

    def assign(
        self, target: n.LValue, value: TypeUnion, typed: bool = True
    ) -> TypeUnion:
        if isinstance(target, n.Name):
            log.debug(f"Assigning {value} to {target.id}_{target.set_count}")
            var_expr = self.visit(target)
            var_name = cast(VariableTypeUnion, var_expr).name
            if typed:
                self.type_manager.put(var_name, value.sorts)
            var = self.registrar.make_any(var_name)
            return self.registrar.assign(var, value)
        elif isinstance(target, n.Attribute):
            log.debug(f"Assigning {value} to {target.value}.{target.attr}")
            if target.attr == "left":
                other_attr = "right"
            elif target.attr == "right":
                other_attr = "left"
            else:
                raise GenerationError(f"Unexpected attribute {target.attr}")

            other_value: TypeUnion = self.visit(
                n.Attribute(e=target.e, value=target.e, attr=other_attr)
            )
            this_value: TypeUnion = self.visit(
                n.Attribute(e=target.e, value=target.e, attr=target.attr)
            )
            dest = self.visit(target.e)
            if isinstance(dest, ExpandableTypeUnion):
                dest = dest.expand()
            pair = getattr(self.registrar.reftype, "Pair")
            wrap = self.registrar.wrap
            store = self.store

            if target.attr == "left":
                left_value = value
                right_value = other_value
            else:
                left_value = other_value
                right_value = value

            class UpdateMagic(Magic):
                @magic(Reference, object, object)
                def write(
                    self, dest: ReferenceT, left: Expression, right: Expression
                ) -> z3.BoolRef:
                    log.debug("Magic update for {} with {} {}", dest, left, right)
                    left_val = wrap(left)
                    right_val = wrap(right)
                    store._set(dest, pair(left_val, right_val))
                    return BOOL_TRUE

            return UpdateMagic(self.sorting)(dest, left_value, right_value)

        raise RuntimeError(
            f"Unexpected target type {type(target)} of assign target {target}"
        )

    def visit_Expr(self, node: n.Expr[Any]) -> TypeUnion:
        v = self.visit(node.value)
        assert v is not None
        return v

    def visit_Call(self, node: n.Call) -> TypeUnion:
        log.info(f"Found call to {node.func}")
        if isinstance(node.func, n.Name):
            function = node.func.id
            if function == "input":
                raise GenerationError("`input` not supported in tested code")
            args = [self.visit(v) for v in node.args]
            for constructor in self.registrar.ref_constructors():
                log.debug(f"Trying {constructor.name()} on {function}")
                if constructor.name() == function:
                    assert len(node.keywords) == 0
                    union = self.construct_call(constructor, args)
                    log.debug(f"Constructed result is {union}")
                    return union
            builtin = self.builtins.get(function, None)
            if builtin is not None:
                log.debug(f"{function} is a builtin: adding call")
                union = builtin(*args)
                log.debug(f"Builtin result is {union}")
                return union
            ignore = CExpr(BOOL_TRUE, {("ignore", z3.BoolSort(), BOOL_FALSE)})
            return TypeUnion([ignore], {z3.BoolSort()})

        # Treat functions as true which we couldn't substitute
        raise GenerationError(
            f"Function call {node} is not a name; cannot call function expressions"
        )

    def construct_call(
        self, constructor: Callable[..., Expression], args: Sequence[TypeUnion]
    ) -> TypeUnion:

        exprs = []
        sorts: SortSet = set()
        for arg_tuple in Magic.cartesian_product(args):
            target = constructor(*(self.registrar.wrap(e.expr) for e in arg_tuple))
            expr = self.store.add(cast(z3.DatatypeRef, target))
            constraints = set(mapcat(lambda x: x.constraints, arg_tuple))
            if len(constraints) > 0:
                cexpr = CExpr(expr=expr, constraints=constraints)
            else:
                cexpr = CExpr(expr=expr)
            exprs.append(cexpr)
            sorts.add(expr.sort())
        if len(exprs) == 0 and any(
            isinstance(arg, ExpandableTypeUnion) for arg in args
        ):
            newargs = Magic.expand(args)
            return self.construct_call(constructor, newargs)
        return TypeUnion(expressions=exprs, sorts=sorts)

    def visit_ReturnResult(self, node: n.ReturnResult) -> TypeUnion:
        variable = get_result(node)
        var = self.registrar.make_any(variable)
        if node.value:
            expr = self.visit(node.value)
            self.type_manager.put(variable, expr.sorts)
            return self.registrar.assign(var, expr)
        else:
            raise RuntimeError(
                "Cannot use return value of function without return value"
            )


class OperatorConverter(SimpleVisitor[OpFunc]):
    def __init__(
        self, store: Store, registrar: TypeRegistrar, fount: MagicFountain
    ) -> None:
        self.store = store
        self.registrar = registrar
        self.fount = fount

    def visit_Add(self, node: n.Add) -> OpFunc:
        class AddMagic(Magic):
            @magic(IntSort, IntSort)
            def addInt(self, left: z3.Int, right: z3.Int) -> z3.Int:
                return left + right

            @magic(StringSort, StringSort)
            def addString(self, left: z3.String, right: z3.String) -> z3.String:
                return z3.Concat(left, right)

        return AddMagic(self.fount.sorting)

    def visit_Sub(self, node: n.Sub) -> OpFunc:
        return self.fount(IntSort, IntSort)(operator.sub)

    def visit_Mult(self, node: n.Mult) -> OpFunc:
        return self.fount(IntSort, IntSort)(operator.mul)

    def visit_Div(self, node: n.Div) -> OpFunc:
        class DivMagic(Magic):
            @magic(IntSort, IntSort, constraint=(lambda n, d: {d != z3.IntVal(0)}))
            def divInts(self, left: z3.Int, right: z3.Int) -> z3.Real:
                left_real = z3.ToReal(left)
                right_real = z3.ToReal(right)
                return left_real / right_real

            @magic(IntSort, RealSort, constraint=(lambda n, d: {d != z3.IntVal(0)}))
            def divIntReal(self, left: z3.Int, right: z3.Real) -> z3.Real:
                return left / right

            @magic(RealSort, ArithSort, constraint=(lambda n, d: {d != z3.IntVal(0)}))
            def divReal(self, left: z3.Real, right: z3.ArithRef) -> z3.Real:
                return left / right

        return DivMagic(self.fount.sorting)

    def visit_FloorDiv(self, node: n.FloorDiv) -> OpFunc:
        return self.fount(
            IntSort, IntSort, constraint=(lambda n, d: {d != z3.IntVal(0)})
        )(operator.truediv)

    def visit_Mod(self, node: n.Mod) -> OpFunc:
        return self.fount(IntSort, IntSort)(operator.mod)

    def visit_LtE(self, node: n.LtE) -> OpFunc:
        return self.fount(IntSort, IntSort)(operator.le)

    def visit_GtE(self, node: n.GtE) -> OpFunc:
        return self.fount(IntSort, IntSort)(operator.ge)

    def visit_Or(self, node: n.Or) -> OpFunc:
        return self.fount(BoolSort, BoolSort)(lambda *a: bool_or([*a]))

    def visit_And(self, node: n.And) -> OpFunc:
        return self.fount(BoolSort, BoolSort)(lambda *a: bool_and([*a]))

    def visit_Eq(self, node: n.Eq) -> OpFunc:
        return EqMagic(self.fount.sorting, self.store, self.registrar.reftype)

    def visit_Is(self, node: n.Is) -> OpFunc:
        return IsMagic(self.fount.sorting)

    def visit_IsNot(self, node: n.IsNot) -> OpFunc:
        return IsNotMagic(self.fount.sorting)

    def visit_NotEq(self, node: n.NotEq) -> OpFunc:
        return NotEqMagic(self.fount.sorting, self.store, self.registrar.reftype)

    def visit_Lt(self, node: n.Lt) -> OpFunc:
        return self.fount(IntSort, IntSort)(operator.lt)

    def visit_Gt(self, node: n.Gt) -> OpFunc:
        return self.fount(IntSort, IntSort)(operator.gt)

    def visit_Not(self, node: n.Not) -> OpFunc:
        def not_func(value: TypeUnion) -> TypeUnion:
            return self.store.to_boolean(value, invert=True)

        return not_func

    def visit_USub(self, node: n.USub) -> OpFunc:
        return self.fount(IntSort)(lambda x: -x)  # type: ignore


def get_variable(name: str, idx: int) -> str:
    name = "pyname_" + name

    if idx == 0:
        return name
    else:
        return name + "_" + str(idx)


def get_variable_name(node: n.Name) -> str:
    name = "pyname_" + node.id

    if node.set_count == 0:
        return name
    else:
        return name + "_" + str(node.set_count)


def get_prefix(prefix: n.Prefix) -> str:
    return f"function_{prefix.func}_{prefix.number}"


def get_result(prefix: n.Prefix) -> str:
    return get_prefix(prefix) + "_return"


def get_prefixed_variable(prefixed_name: n.PrefixedName) -> str:
    prefix = get_prefix(prefixed_name)
    variable = get_variable(prefixed_name.id, prefixed_name.set_count)
    return prefix + "_" + variable


class IsMagic(Magic):
    def should_expand(self, *args: TypeUnion) -> bool:
        left, right = args
        if not isinstance(left, ExpandableTypeUnion):
            return True
        if not isinstance(right, ExpandableTypeUnion):
            return True
        return False

    @magic(z3.SortRef, z3.SortRef)
    def equality(self, left: Expression, right: Expression) -> z3.BoolRef:
        left_sort = left.sort()
        right_sort = right.sort()
        if left_sort == right_sort:
            return self.compare(left, right)
        else:
            # If the argument sorts are different, the values are different.
            return z3.BoolVal(False)

    def compare(self, left: Expression, right: Expression) -> z3.BoolRef:
        return left == right


class EqMagic(IsMagic):
    def __init__(
        self, sorting: SortingFunc, store: Store, reftype: Optional[z3.DatatypeSortRef]
    ) -> None:
        super().__init__(sorting)
        self.store = store
        self.reftype = reftype

    def compare(self, left: Expression, right: Expression) -> z3.BoolRef:
        if left.sort() == Reference:
            assert self.reftype is not None
            assert left.sort() == Reference
            assert right.sort() == Reference
            left_val = self.store.get(cast(ReferenceT, left))
            right_val = self.store.get(cast(ReferenceT, right))

            p_left = getattr(self.reftype, "Pair_left", None)
            p_right = getattr(self.reftype, "Pair_right", None)
            assert p_left is not None
            assert p_right is not None

            return bool_and(
                (
                    p_left(left_val) == p_left(right_val),
                    p_right(left_val) == p_right(right_val),
                )
            )
        else:
            return left == right


class IsNotMagic(Magic):
    def should_expand(self, *args: TypeUnion) -> bool:
        left, right = args
        if not isinstance(left, ExpandableTypeUnion):
            return True
        if not isinstance(right, ExpandableTypeUnion):
            return True
        return False

    @magic(z3.SortRef, z3.SortRef)
    def inequality(self, left: Expression, right: Expression) -> z3.BoolRef:
        left_sort = left.sort()
        right_sort = right.sort()
        if left_sort == right_sort:
            return self.compare(left, right)
        else:
            return z3.BoolVal(True)

    def compare(self, left: Expression, right: Expression) -> z3.BoolRef:
        return left != right


class NotEqMagic(IsNotMagic):
    def __init__(
        self, sorting: SortingFunc, store: Store, reftype: Optional[z3.DatatypeSortRef]
    ) -> None:
        super().__init__(sorting)
        self.store = store
        self.reftype = reftype

    def compare(self, left: Expression, right: Expression) -> z3.BoolRef:
        if left.sort() == Reference:
            assert self.reftype is not None
            assert left.sort() == Reference
            assert right.sort() == Reference
            left_val = self.store.get(cast(ReferenceT, left))
            right_val = self.store.get(cast(ReferenceT, right))

            p_left = getattr(self.reftype, "Pair_left", None)
            p_right = getattr(self.reftype, "Pair_right", None)
            assert p_left is not None
            assert p_right is not None

            return bool_or(
                (
                    p_left(left_val) != p_left(right_val),
                    p_right(left_val) != p_right(right_val),
                )
            )
        else:
            return left != right


class TupleError(NotImplementedError):
    pass
