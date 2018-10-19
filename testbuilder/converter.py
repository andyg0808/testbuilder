"""
Converts an expression from Python AST into a z3 expression. The structural
aspects of converting Python are handled by the code in expression_builder.
"""
from __future__ import annotations

import operator
import re
from functools import singledispatch
from typing import Any, Callable, Mapping, Optional, Type, TypeVar, Union, cast

import z3

from . import nodetree as n
from .visitor import SimpleVisitor
from .z3_types import (
    Any as AnyType,
    AnyT,
    ConstrainedExpression as CExpr,
    Expression,
    MoreMagic as Magic,
    TypeRegistrar,
    TypeUnion,
    make_any,
    more_magic_tag as magic,
)

OpFunc = Callable[..., TypeUnion]
TypeRegex = re.compile(r"^(?:([A-Z])_)?(.+)$", re.IGNORECASE)
TypeConstructor = Callable[[str], Expression]


Constants: Mapping[Any, TypeUnion] = {
    True: TypeUnion.wrap(z3.BoolVal(True)),
    False: TypeUnion.wrap(z3.BoolVal(False)),
}

Registrar = TypeRegistrar(AnyType)

Typelist: Mapping[str, TypeConstructor] = {
    "b": z3.Bool,
    "i": z3.Int,
    "s": z3.String,
    "a": make_any,
}

IntSort = z3.IntSort()
StringSort = z3.StringSort()
BoolSort = z3.BoolSort()


class ExpressionConverter(SimpleVisitor[TypeUnion]):
    def __init__(self) -> None:
        super().__init__()
        self.visit_oper = OperatorConverter()

    def visit_Int(self, node: n.Int) -> TypeUnion:
        return TypeUnion.wrap(z3.IntVal(node.v))

    def visit_Str(self, node: n.Str) -> TypeUnion:
        return TypeUnion.wrap(z3.StringVal(node.s))

    def visit_BinOp(self, node: n.BinOp) -> TypeUnion:
        op = self.visit_oper(node.op)
        return op(self.visit(node.left), self.visit(node.right))

    def visit_UnaryOp(self, node: n.UnaryOp) -> TypeUnion:
        op = self.visit_oper(node.op)
        return op(self.visit(node.operand))

    def visit_Return(self, node: n.Return) -> TypeUnion:
        if node.value:
            expr = self.visit(node.value)
            return Registrar.assign(make_any("ret"), expr)
        else:
            return TypeUnion.wrap(z3.BoolVal(True))

    def visit_NameConstant(self, node: n.NameConstant) -> TypeUnion:
        return Constants[node.value]

    def visit_Name(self, node: n.Name) -> TypeUnion:
        variable = get_variable(node.id, node.set_count)
        # constructor = get_type(node.id, node.set_count)
        # Add cache support here
        return Registrar.AllTypes(variable)

    def visit_PrefixedName(self, node: n.PrefixedName) -> TypeUnion:
        prefix = get_prefix(node)
        variable = get_variable(node.id, node.set_count)
        return Registrar.AllTypes(prefix + "_" + variable)

    def visit_Result(self, node: n.Result) -> TypeUnion:
        variable = get_result(node)
        return Registrar.AllTypes(variable)

    def visit_Set(self, node: n.Set) -> TypeUnion:
        # We know `target` is a Name
        target = node.target
        var = make_any(get_variable(target.id, target.set_count))
        value = self.visit(node.e)
        return Registrar.assign(var, value)

    def visit_Expr(self, node: n.Expr) -> TypeUnion:
        v = self.visit(node.value)
        assert v is not None
        return v

    def visit_Call(self, node: n.Call) -> TypeUnion:
        # Temporarily treat functions as true
        return TypeUnion.wrap(z3.BoolVal(True))

    def visit_ReturnResult(self, node: n.ReturnResult) -> TypeUnion:
        var = make_any(get_result(node))
        if node.value:
            expr = self.visit(node.value)
            return Registrar.assign(var, expr)
        else:
            return Registrar.assign(var, expr)


class OperatorConverter(SimpleVisitor[OpFunc]):
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
        return Magic.m(BoolSort, BoolSort)(z3.Or)

    def visit_And(self, node: n.And) -> OpFunc:
        return Magic.m(BoolSort, BoolSort)(z3.And)

    def visit_Eq(self, node: n.Eq) -> OpFunc:
        return Magic.m(object, object)(operator.eq)

    def visit_Lt(self, node: n.Lt) -> OpFunc:
        return Magic.m(z3.ArithSortRef, z3.ArithSortRef)(operator.lt)

    def visit_Gt(self, node: n.Gt) -> OpFunc:
        return Magic.m(IntSort, IntSort)(operator.gt)

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


def to_boolean(value: TypeUnion, invert: bool = False) -> z3.Bool:
    """
    Forcibly convert a TypeUnion to a boolean. Will apply truthy
    standards if needed in order to avoid problems.
    """
    if value.is_bool():
        return value.to_expr(invert)
    else:
        return Registrar.to_boolean(value).to_expr(invert)


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


def get_type(name: str, set_count: int) -> TypeConstructor:
    match = TypeRegex.match(name)
    if match and match.group(1):
        # There was a type given for the variable. Use that.
        return Typelist[match.group(1).lower()]
    else:
        # It's not got a type. Assume it's an integer.
        return z3.Int
