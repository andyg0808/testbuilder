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
from .ast_builder import AstBuilder

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


class ConversionVisitor(ast.NodeVisitor):
    def __init__(self, variables: MMapping[str, int]) -> None:
        super().__init__()
        self.variables = variables
        # self.expression has to be Any because we put varying types of values
        # in it depending on where we are in the AST. The benefit of making it
        # properly typed doesn't seem worth the bother.
        self.expression: Any = None
        self.assigning = False

    def visit_Num(self, node: ast.Num) -> None:
        if isinstance(node.n, int):
            self.expression = z3.IntVal(node.n)
        else:
            raise RuntimeError("Unknown number")

    def visit_Str(self, node: ast.Str) -> None:
        self.expression = z3.StringVal(node.s)

    def visit_Assign(self, node: ast.Assign) -> None:
        print("assign")
        # TODO: Support multiple assignment
        value = self.get_expr(node.value)
        self.assigning = True
        target = self.get_expr(node.targets[0])
        self.assigning = False
        self.expression = target == value

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        print("Aug assign")
        value = self.get_expr(node.value)
        old_target = self.get_expr(node.target)
        op = self.get_expr(node.op)
        self.assigning = True
        target = self.get_expr(node.target)
        self.assigning = False
        self.expression = target == op(old_target, value)

    def visit_BinOp(self, node: ast.BinOp) -> None:
        left = self.get_expr(node.left)
        right = self.get_expr(node.right)
        self.expression = self.get_expr(node.op)(left, right)

    def get_expr(self, node: ast.AST) -> Any:
        self.visit(node)
        return self.expression

    def visit_BoolOp(self, node: ast.BoolOp) -> None:
        op = self.get_expr(node.op)
        value_list = [self.get_expr(v) for v in node.values]
        self.expression = reduce(op, value_list)

    def visit_Compare(self, node: ast.Compare) -> None:
        left = self.get_expr(node.left)
        ops = map(self.get_expr, node.ops)
        comparators = map(self.get_expr, node.comparators)

        def combine(
            left: Expression, zipped: Tuple[Callable[..., Expression], Expression]
        ) -> Expression:
            op, right = zipped
            return op(left, right)

        self.expression = reduce(combine, zip(ops, comparators), left)

    def visit_Call(self, node: ast.Call) -> None:
        self.expression = z3.BoolVal(True)

    def visit_UnaryOp(self, node: ast.UnaryOp) -> None:
        op = self.get_expr(node.op)
        operand = self.get_expr(node.operand)
        self.expression = op(operand)

    def visit_Return(self, node: ast.Return) -> None:
        if node.value:
            expr = self.get_expr(node.value)
            self.expression = z3.Int("ret") == expr
        else:
            self.expression = z3.BoolVal(True)

    def visit_Name(self, node: ast.Name) -> None:
        idx = self.variables.get(node.id, VAR_START_VALUE)
        if self.assigning:
            # If the node id is not in self.variables then we want to use 0 as
            # the initial value.
            if node.id in self.variables:
                idx += 1
            self.variables[node.id] = idx

        if node.id == "s":
            self.expression = z3.String(get_variable(node.id, idx))
        else:
            self.expression = z3.Int(get_variable(node.id, idx))

    def visit_NameConstant(self, node: ast.NameConstant) -> None:
        self.expression = Constants[node.value]

    def visit_Add(self, node: ast.Add) -> None:
        self.expression = operator.add

    def visit_Sub(self, node: ast.Sub) -> None:
        self.expression = operator.sub

    def visit_Mult(self, node: ast.Mult) -> None:
        self.expression = operator.mul

    def visit_Div(self, node: ast.Div) -> None:
        self.expression = operator.truediv

    def visit_Eq(self, node: ast.Eq) -> None:
        self.expression = operator.eq

    def visit_Lt(self, node: ast.Lt) -> None:
        self.expression = operator.lt

    def visit_LtE(self, node: ast.LtE) -> None:
        self.expression = operator.le

    def visit_Gt(self, node: ast.Gt) -> None:
        self.expression = operator.gt

    def visit_GtE(self, node: ast.GtE) -> None:
        self.expression = operator.ge

    def visit_And(self, node: ast.And) -> None:
        self.expression = z3.And

    def visit_Or(self, node: ast.Or) -> None:
        self.expression = z3.Or

    def visit_USub(self, node: ast.USub) -> None:
        self.expression = lambda x: -x


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


def convert(code: ast.AST, variables: MMapping[str, int]) -> Expression:
    # v = ConversionVisitor(variables)
    # return cast(Expression, v.get_expr(code))
    print("code type", type(code))
    ab = AstBuilder(variables)
    z3c = Z3Converter()
    tree = ab.visit(code)
    print("ast type", type(tree))
    expr = z3c.visit(tree)
    print("z3 type", type(expr))
    assert expr is not None
    return expr
