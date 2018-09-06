"""
Converts an expression from Python AST into a z3 expression. The structural
aspects of converting Python are handled by the code in expression_builder.
"""
import operator
from functools import singledispatch
from typing import Any, Callable, Mapping, TypeVar, cast

import z3

from . import nodetree as n

Expression = z3.ExprRef

Constants: Mapping[Any, Expression] = {True: z3.BoolVal(True), False: z3.BoolVal(False)}

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


def get_result(func: str, number: int) -> str:
    return f"function_{func}_{number}_return"


OpFunc = Callable[..., Expression]


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
    if node.id == "s":
        return z3.String(variable)
    else:
        return z3.Int(variable)


@visit_expr.register(n.Result)
def visit_Result(node: n.Result) -> Expression:
    variable = get_result(node.func, node.number)
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
    var = z3.Int(get_result(node.func, node.number))
    if node.value:
        expr = visit_expr(node.value)
        return var == expr
    else:
        return var == z3.BoolVal(True)


def convert(tree: n.Node) -> Expression:
    expr = visit_expr(tree)
    assert expr is not None
    return expr
