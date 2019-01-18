"""
Converts an expression from Python AST into a z3 expression. The
structural aspects of converting Python are handled by the code in
`ssa_to_expression`.
"""
from __future__ import annotations

import operator
import re
from functools import reduce
from typing import Any, Callable, Mapping, Sequence, cast

import z3
from logbook import Logger
from toolz import groupby, mapcat

from . import nodetree as n
from .constrained_expression import ConstrainedExpression as CExpr, ConstraintSet
from .expandable_type_union import ExpandableTypeUnion
from .expression_type_union import ExpressionTypeUnion
from .magic import Magic, magic_tag as magic
from .store import Store
from .type_manager import TypeManager
from .type_registrar import TypeRegistrar
from .type_union import TypeUnion
from .variable_type_union import VariableTypeUnion
from .visitor import SimpleVisitor
from .z3_types import (
    BOOL_TRUE,
    Expression,
    Reference,
    ReferenceT,
    SortSet,
    bool_and,
    bool_or,
)

log = Logger("converter")

OpFunc = Callable[..., TypeUnion]
TypeRegex = re.compile(r"^(?:([A-Z])_)?(.+)$", re.IGNORECASE)
TypeConstructor = Callable[[str], Expression]


IntSort = z3.IntSort()
StringSort = z3.StringSort()
BoolSort = z3.BoolSort()


class ExpressionConverter(SimpleVisitor[TypeUnion]):
    def __init__(
        self, registrar: TypeRegistrar, type_manager: TypeManager, store: Store
    ) -> None:
        super().__init__()
        self.visit_oper = OperatorConverter(store)
        self.registrar = registrar
        self.type_manager = type_manager
        self.store = store
        self.constants: Mapping[Any, TypeUnion] = {
            True: TypeUnion.wrap(z3.BoolVal(True)),
            False: TypeUnion.wrap(z3.BoolVal(False)),
        }
        none = getattr(self.registrar.anytype, "none", None)
        if none is not None:
            self.constants[None] = TypeUnion.wrap(none)

    def visit_Int(self, node: n.Int) -> TypeUnion:
        return TypeUnion.wrap(z3.IntVal(node.v))

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
            self.type_manager.put(varname, {c[1] for c in constraints})
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
        return Magic.m(Reference)(self.store.get)(val)

    def visit_Attribute(self, node: n.Attribute) -> TypeUnion:
        value = self.visit(node.value)
        attr = node.attr
        assert attr in ["left", "right"]
        assert (
            self.registrar.reftype is not None
        ), "Need reference types enabled to use attributes"

        accessor = getattr(self.registrar.reftype, "Pair_" + attr)

        dereferenced = self.dereference(value)
        component = Magic.m(self.registrar.reftype)(accessor)(dereferenced)
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

    def visit_Assert(self, node: n.Assert) -> TypeUnion:
        expr = self.visit(node.test)
        return expr

    def assign(self, target: n.LValue, value: TypeUnion) -> TypeUnion:
        if isinstance(target, n.Name):
            log.debug(f"Assigning {value} to {target.id}_{target.set_count}")
            var_expr = self.visit(target)
            var_name = cast(VariableTypeUnion, var_expr).name
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
                raise RuntimeError(f"Unexpected attribute {target.attr}")

            other_value: TypeUnion = self.visit(
                n.Attribute(e=target.e, value=target.e, attr=other_attr)
            )
            this_value: TypeUnion = self.visit(
                n.Attribute(e=target.e, value=target.e, attr=target.attr)
            )
            dest = self.visit(target.e)
            # print("updating type manager from", self.type_manager)
            # self.type_manager.put(
            #     cast(VariableTypeUnion, self.visit(target.e.find_name())).name,
            #     {Reference},
            # )
            # self.type_manager.put(
            #     str(this_value.unwrap(choice=Reference)), {value.sorts}
            # )
            # print("updated type manager to", self.type_manager)
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

            return UpdateMagic()(dest, left_value, right_value)

        raise RuntimeError(
            f"Unexpected target type {type(target)} of assign target {target}"
        )

    def visit_Expr(self, node: n.Expr) -> TypeUnion:
        v = self.visit(node.value)
        assert v is not None
        return v

    def visit_Call(self, node: n.Call) -> TypeUnion:
        log.info(f"Found call to {node.func}")
        if isinstance(node.func, n.Name):
            function = node.func.id
            for constructor in self.registrar.ref_constructors():
                log.debug(f"Trying {constructor.name()} on {function}")
                if constructor.name() == function:
                    args = [self.visit(v) for v in node.args]
                    assert len(node.keywords) == 0
                    union = self.construct_call(constructor, args)
                    log.debug(f"Constructed result is {union}")
                    return union

        # Treat functions as true which we couldn't substitute
        return TypeUnion.wrap(z3.BoolVal(True))

    def construct_call(
        self, constructor: z3.FuncDeclRef, args: Sequence[TypeUnion]
    ) -> TypeUnion:

        print("Constructing call", constructor, args)
        exprs = []
        sorts: SortSet = set()
        for arg_tuple in Magic.cartesian_product(args):
            print("running for", arg_tuple)
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
    def __init__(self, store: Store) -> None:
        self.store = store

    def visit_Add(self, node: n.Add) -> OpFunc:
        class AddMagic(Magic):
            @magic(IntSort, IntSort)
            def addInt(self, left: z3.Int, right: z3.Int) -> z3.Int:
                return left + right

            @magic(StringSort, StringSort)
            def addString(self, left: z3.String, right: z3.String) -> z3.String:
                return z3.Concat(left, right)

        return AddMagic()

    def visit_Sub(self, node: n.Sub) -> OpFunc:
        return Magic.m(IntSort, IntSort)(operator.sub)

    def visit_Mult(self, node: n.Mult) -> OpFunc:
        return Magic.m(IntSort, IntSort)(operator.mul)

    def visit_Div(self, node: n.Div) -> OpFunc:
        return Magic.m(IntSort, IntSort)(operator.truediv)

    def visit_LtE(self, node: n.LtE) -> OpFunc:
        return Magic.m(IntSort, IntSort)(operator.le)

    def visit_GtE(self, node: n.GtE) -> OpFunc:
        return Magic.m(IntSort, IntSort)(operator.ge)

    def visit_Or(self, node: n.Or) -> OpFunc:
        return Magic.m(BoolSort, BoolSort)(lambda *a: bool_or([*a]))

    def visit_And(self, node: n.And) -> OpFunc:
        return Magic.m(BoolSort, BoolSort)(lambda *a: bool_and([*a]))

    def visit_Eq(self, node: n.Eq) -> OpFunc:
        class EqMagic(Magic):
            def should_expand(self, *args: TypeUnion) -> bool:
                left, right = args
                if not isinstance(left, ExpandableTypeUnion):
                    return True
                if not isinstance(right, ExpandableTypeUnion):
                    return True
                print("not expanding")
                return False

            @magic(z3.SortRef, z3.SortRef)
            def equality(self, left: Expression, right: Expression) -> z3.BoolRef:
                left_sort = left.sort()
                right_sort = right.sort()
                if left_sort == right_sort:
                    return left == right
                else:
                    # If the argument sorts are different, the values are different.
                    return z3.BoolVal(False)

        return EqMagic()

    def visit_NotEq(self, node: n.NotEq) -> OpFunc:
        class NotEqMagic(Magic):
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
                    return left != right
                else:
                    return z3.BoolVal(True)

        return NotEqMagic()

    def visit_Lt(self, node: n.Lt) -> OpFunc:
        return Magic.m(z3.ArithSortRef, z3.ArithSortRef)(operator.lt)

    def visit_Gt(self, node: n.Gt) -> OpFunc:
        return Magic.m(IntSort, IntSort)(operator.gt)

    def visit_Not(self, node: n.Not) -> OpFunc:
        def not_func(value: TypeUnion) -> TypeUnion:
            return self.store.to_boolean(value, invert=True)

        return not_func

    def visit_USub(self, node: n.USub) -> OpFunc:
        return Magic.m(IntSort)(lambda x: -x)


# T = TypeVar("T")


# def safify(
#     exception: Type[BaseException], op: Callable[..., T]
# ) -> Callable[..., Optional[T]]:
#     def _safify(*args: Any, **kwargs: Any) -> Optional[T]:
#         try:
#             return op(*args, **kwargs)
#         except exception as e:
#             return None

#     return _safify


# Options:
# * Map == between the z3 variable and the values (which have to be wrapped)
# * Map == between each element of the unwrapped z3 variable and the values

# Not options:
# * Can't do If(cond, case1, If(cond2, case2, ...)) # because final
#   else has no good return value
#


# E = TypeVar("E", bound=n.expr)
# B = TypeVar("B")


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
