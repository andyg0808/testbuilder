"""
Converts an expression from Python AST into a z3 expression. The structural
aspects of converting Python are handled by the code in expression_builder.
"""
from __future__ import annotations

import operator
import re
from functools import singledispatch
from typing import Any, Callable, Mapping, Type, TypeVar, cast

import z3

from . import nodetree as n
from .z3_types import Any as AnyType, AnyT, Expression, make_any

OpFunc = Callable[..., Expression]
TypeRegex = re.compile(r"^(?:([A-Z])_)?(.+)$", re.IGNORECASE)
TypeConstructor = Callable[[str], Expression]


Constants: Mapping[Any, Expression] = {True: z3.BoolVal(True), False: z3.BoolVal(False)}
# We need to store all the separate possible values, along with what
# their types are?

# We're then going to take a pair of these and define the correct
# operations pairwise across the cartesian product of the types

# We replace each statement with a modified version which will
# ultimately write its result into an appropriate variable. If all
# results are a single type, they will end up in some kind of
# container (either a single-type Any variable, or a variable of the
# specific type we're interested in). If they are of various types,
# they will be conglomerated into a single Any variable with multiple
# values.

# These Any type variables need to be represented for our purposes by
# a data structure which allows us access to all the separate values
# of each type. This allows us to have a better approximation of the
# type system, rather than needing to handle every Any type as though
# it could actually have _any_ type in it. For variables which we
# _don't_ have any type restrictions on, we have to handle every
# possible type case. However, we can ignore some type cases, in which
# case, they will not be legal to assign to that variable, because the
# values ending up in the TypeUnion structure will dictate the
# constraints put on the value of the variable represented by the
# TypeUnion structure.

# The TypeUnion structure will need to track the per-type conditions
# on variables which are part of the expression it contains. For
# example, if we have a TypeUnion with an Int and a Bool value, and
# the same variable is used in both, we need to add two separate
# constraints to the resulting expression: first, if we take the Int
# path, the input variable needs to contain an Int, and second, if we
# take the Bool path, the input variable needs to contain a Bool.

# These TypeUnion values will need to be used during the symbolic
# execution of each value. Since the only statement contexts using
# expressions are Exprs and TrueBranch/FalseBranches, we can add the
# appropriate expressions into a larger expression which is output
# there. (I.e., the result is expected to be a boolean, not an
# expression with some other type of result.)

#
Typelist: Mapping[str, TypeConstructor] = {
    "b": z3.Bool,
    "i": z3.Int,
    "s": z3.String,
    "a": make_any,
}

VAR_START_VALUE = 0


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


@singledispatch
def visit_expr(node: n.expr) -> Expression:
    raise RuntimeError(f"Unimplemented handler for {type(node)}")


@singledispatch
def visit_oper(node: n.Operator) -> OpFunc:
    name = type(node).__name__
    op = getattr(operator, name.lower(), None)
    if op is not None:
        return cast(OpFunc, op)
    else:
        op = getattr(z3, name, None)
        if op is not None:
            return op
        else:
            raise RuntimeError(f"Unknown node type {type(node)}")


@visit_expr.register(n.Int)
def visit_Int(node: n.Int) -> z3.Int:
    return z3.IntVal(node.v)


@visit_expr.register(n.Str)
def visit_Str(node: n.Str) -> z3.StringVal:
    return z3.StringVal(node.s)


@visit_expr.register(n.BinOp)
def visit_BinOp(node: n.BinOp) -> Expression:
    op = visit_oper(node.op)
    return op(visit_expr(node.left), visit_expr(node.right))


@visit_oper.register(n.Mult)
def visit_Mult(node: n.Mult) -> OpFunc:
    return operator.mul


@visit_oper.register(n.Div)
def visit_Div(node: n.Div) -> OpFunc:
    return operator.truediv


@visit_oper.register(n.LtE)
def visit_LtE(node: n.LtE) -> OpFunc:
    return operator.le


@visit_oper.register(n.GtE)
def visit_GtE(node: n.GtE) -> OpFunc:
    return operator.ge


@visit_oper.register(n.USub)
def visit_USub(node: n.USub) -> OpFunc:
    return operator.neg


@visit_expr.register(n.UnaryOp)
def visit_UnaryOp(node: n.UnaryOp) -> Expression:
    op = visit_oper(node.op)
    operand = visit_expr(node.operand)
    return op(operand)


@visit_expr.register(n.Return)
def visit_Return(node: n.Return) -> Expression:
    if node.value:
        expr = visit_expr(node.value)
        return z3.Int("ret") == expr
    else:
        return z3.BoolVal(True)


@visit_expr.register(n.NameConstant)
def visit_NameConstant(node: n.NameConstant) -> Expression:
    return Constants[node.value]


@visit_expr.register(n.Name)
def visit_Name(node: n.Name) -> Expression:
    variable = get_variable(node.id, node.set_count)
    constructor = get_type(node.id, node.set_count)
    return constructor(variable)


@visit_expr.register(n.PrefixedName)
def visit_PrefixedName(node: n.PrefixedName) -> Expression:
    prefix = get_prefix(node)
    variable = get_variable(node.id, node.set_count)
    return z3.Int(prefix + "_" + variable)


@visit_expr.register(n.Result)
def visit_Result(node: n.Result) -> Expression:
    variable = get_result(node)
    return z3.Int(variable)


@visit_expr.register(n.Set)
def visit_Set(node: n.Set) -> Expression:
    var = visit_expr(node.target)
    value = visit_expr(node.e)
    return var == value


E = TypeVar("E", bound=n.expr)
B = TypeVar("B")


@visit_expr.register(n.Expr)
def visit_Expr(node: n.Expr[E]) -> Expression:
    v = visit_expr(node.value)
    assert v is not None
    return v


@visit_expr.register(n.Call)
def visit_Call(node: n.Call) -> z3.BoolVal:
    # Temporarily treat functions as true
    return z3.BoolVal(True)


@visit_expr.register(n.ReturnResult)
def visit_ReturnResult(node: n.ReturnResult) -> Expression:
    var = z3.Int(get_result(node))
    if node.value:
        expr = visit_expr(node.value)
        return var == expr
    else:
        return var == z3.BoolVal(True)


def convert(tree: n.Node) -> Expression:
    expr = visit_expr(tree)
    assert expr is not None
    return expr
