"""
Converts an expression from Python AST into a z3 expression. The structural
aspects of converting Python are handled by the code in expression_builder.
"""
from __future__ import annotations

import operator
import re
from typing import Any, Callable, Mapping, Sequence, Tuple, cast

from toolz import groupby, mapcat

import z3

from . import nodetree as n
from .constrained_expression import ConstrainedExpression as CExpr
from .magic import Magic, magic_tag as magic
from .type_manager import TypeManager
from .type_registrar import TypeRegistrar
from .type_union import TypeUnion
from .utils import crash
from .variable_type_union import VariableTypeUnion
from .visitor import SimpleVisitor
from .z3_types import AnyT, Expression, bool_and, bool_or

OpFunc = Callable[..., TypeUnion]
TypeRegex = re.compile(r"^(?:([A-Z])_)?(.+)$", re.IGNORECASE)
TypeConstructor = Callable[[str], Expression]


Constants: Mapping[Any, TypeUnion] = {
    True: TypeUnion.wrap(z3.BoolVal(True)),
    False: TypeUnion.wrap(z3.BoolVal(False)),
}

IntSort = z3.IntSort()
StringSort = z3.StringSort()
BoolSort = z3.BoolSort()


class ExpressionConverter(SimpleVisitor[TypeUnion]):
    def __init__(self, registrar: TypeRegistrar, type_manager: TypeManager) -> None:
        super().__init__()
        self.visit_oper = OperatorConverter(registrar)
        self.registrar = registrar
        self.type_manager = type_manager

    def visit_Int(self, node: n.Int) -> TypeUnion:
        return TypeUnion.wrap(z3.IntVal(node.v))

    def visit_Str(self, node: n.Str) -> TypeUnion:
        return TypeUnion.wrap(z3.StringVal(node.s))

    def visit_BinOp(self, node: n.BinOp) -> TypeUnion:
        op = self.visit_oper(node.op)
        expr = op(self.visit(node.left), self.visit(node.right))
        var_constraints = mapcat(lambda e: e.constraints, expr.expressions)
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
        return Constants[node.value]

    def visit_Name(self, node: n.Name) -> VariableTypeUnion:
        # TODO: Can any of this be replaced with make_any
        variable = get_variable(node.id, node.set_count)
        sorts = self.type_manager.get(variable)
        if sorts is not None:
            print(f"looked up {variable} and got sorts {sorts}")
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
        # We know `target` is a Name
        target = node.target
        # Since `target` is a Name, it will be converted into a
        # VariableTypeUnion, which has a `name` attribute giving the
        # name of its variable. We do it this way to handle
        # `PrefixedName`s as well as normal `Name`s.
        variable = cast(VariableTypeUnion, self.visit(target)).name
        value = self.visit(node.e)
        var = self.registrar.make_any(variable)
        self.type_manager.put(variable, value.sorts)
        return self.registrar.assign(var, value)

    def visit_Expr(self, node: n.Expr) -> TypeUnion:
        v = self.visit(node.value)
        assert v is not None
        return v

    def visit_Call(self, node: n.Call) -> TypeUnion:
        print("call node", node)
        print(f"type of function: {type(node)}")
        if isinstance(node.func, n.Name):
            function = node.func.id
            for constructor in self.registrar.constructors():
                print(f"trying {constructor.name()} on {function}")
                if constructor.name() == function:
                    args = [self.visit(v) for v in node.args]
                    assert len(node.keywords) == 0
                    union = self.construct_call(constructor, args)
                    print("union is ", union)
                    return union

        # Treat functions as true which we couldn't substitute
        return TypeUnion.wrap(z3.BoolVal(True))

    def construct_call(
        self, constructor: z3.FuncDeclRef, args: Sequence[TypeUnion]
    ) -> TypeUnion:

        print("Constructing call", constructor, args)
        exprs = []
        sorts = set()
        for arg_tuple in Magic.cartesian_product(args):
            print("running for", arg_tuple)
            expr = constructor(*(self.registrar.wrap(e.expr) for e in arg_tuple))
            constraints = list(mapcat(lambda x: x.constraints, arg_tuple))
            if len(constraints) > 0:
                cexpr = CExpr(expr=expr, constraints=list(constraints))
            else:
                cexpr = CExpr(expr=expr)
            exprs.append(cexpr)
            sorts.add(expr.sort())
        if len(exprs) == 0 and any(isinstance(arg, VariableTypeUnion) for arg in args):
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
    def __init__(self, registrar: TypeRegistrar) -> None:
        self.registrar = registrar

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
                if not isinstance(left, VariableTypeUnion):
                    return True
                if not isinstance(right, VariableTypeUnion):
                    return True
                print("not expanding")
                return False

            @magic(z3.SortRef, z3.SortRef)
            def equality(self, left: Expression, right: Expression) -> z3.Bool:
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
                if not isinstance(left, VariableTypeUnion):
                    return True
                if not isinstance(right, VariableTypeUnion):
                    return True
                return False

            @magic(z3.SortRef, z3.SortRef)
            def inequality(self, left: Expression, right: Expression) -> z3.Bool:
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
            return self.registrar.to_boolean(value, invert=True)

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
