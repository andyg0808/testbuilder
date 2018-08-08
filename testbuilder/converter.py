"""
Converts an expression from Python AST into a z3 expression. The structural
aspects of converting Python are handled by the code in expression_builder.
"""
import ast
import operator
from functools import reduce
from typing import Any, Callable, Mapping, MutableMapping as MMapping, Tuple, cast

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


OpFunc = Callable[..., Expression]


class Z3Converter(n.Visitor[Expression]):
    def visit_Int(self, node: n.Int) -> z3.Int:
        return z3.IntVal(node.v)

    def visit_Str(self, node: n.Str) -> z3.StringVal:
        return z3.StringVal(node.s)

    def visit_BinOp(self, node: n.BinOp) -> Expression:
        op = cast(OpFunc, self.visit(node.op))
        return op(self.visit(node.left), self.visit(node.right))

    def visit_Mult(self, node: n.Mult) -> OpFunc:
        return operator.mul

    def visit_Div(self, node: n.Div) -> OpFunc:
        return operator.truediv

    def visit_LtE(self, node: n.LtE) -> OpFunc:
        return operator.le

    def visit_GtE(self, node: n.GtE) -> OpFunc:
        return operator.ge

    def visit_USub(self, node: n.USub) -> OpFunc:
        return operator.neg

    def visit_UnaryOp(self, node: n.UnaryOp) -> Expression:
        op = self.visit(node.op)
        operand = self.visit(node.operand)
        return cast(OpFunc, op)(operand)

    def visit_Return(self, node: n.Return) -> Expression:
        if node.value:
            expr = self.visit(node.value)
            return z3.Int("ret") == expr
        else:
            return z3.BoolVal(True)

    def visit_NameConstant(self, node: n.NameConstant) -> Expression:
        return Constants[node.value]

    def visit_Name(self, node: n.Name) -> Expression:
        variable = get_variable(node.id, node.set_count)
        if node.id == "s":
            return z3.String(variable)
        else:
            return z3.Int(variable)

    def visit_Set(self, node: n.Set) -> Expression:
        var = cast(Expression, self.visit(node.target))
        value = cast(Expression, self.visit(node.e))
        return var == value

    def visit_Expr(self, node: n.Expr) -> Expression:
        v = self.visit(node.value)
        assert v is not None
        return v

    def visit_Call(self, node: n.Call) -> Expression:
        # Temporarily treat functions as true
        return z3.BoolVal(True)

    def generic_visit(self, node: n.Node) -> Any:
        name = type(node).__name__
        op = getattr(operator, name.lower(), None)
        if op is not None:
            return op
        else:
            op = getattr(z3, name, None)
            if op is not None:
                return op
            else:
                raise RuntimeError(f"Unknown node type {type(node)}")


def convert(tree: n.Node) -> Expression:
    z3c = Z3Converter()
    expr = z3c.visit(tree)
    assert expr is not None
    return expr
