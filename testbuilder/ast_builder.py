import ast
from functools import reduce
from typing import (
    Any,
    Callable,
    MutableMapping as MMapping,
    Sequence,
    Tuple,
    Union,
    cast,
)

import dataclasses

from . import nodetree as n

OpFunc = Callable[..., n.expr]

VAR_START_VALUE = 0


class AstBuilder(ast.NodeVisitor):
    def __init__(self, variables: MMapping[str, int]) -> None:
        super().__init__()
        self.variables = variables

    def visit_Num(self, node: ast.Num) -> Union[n.Int, n.Float]:
        if int(node.n) == node.n:
            return n.Int(int(node.n))
        else:
            return n.Float(node.n)

    def get_target_variable(self, node: ast.expr) -> n.Name:
        if isinstance(node, ast.Name):
            var: n.Name = self.visit(node)
            if var.id in self.variables:
                var.set_count += 1
            self.variables[node.id] = var.set_count
            return var
        else:
            raise RuntimeError("Unknown target type")

    def visit_Assign(self, node: ast.Assign) -> n.Set:
        expr = self.visit(node.value)
        target = self.get_target_variable(node.targets[0])
        return n.Set(target, expr)

    def visit_AugAssign(self, node: ast.AugAssign) -> n.Set:
        value = self.visit(node.value)
        var = self.visit(node.target)
        op = self.visit(node.op)
        target = self.get_target_variable(node.target)
        return n.Set(target, n.BinOp(var, op, value))

    # def visit_AugAssign(self, node: ast.AugAssign) -> None:
    #     print("Aug assign")
    #     value = self.get_expr(node.value)
    #     old_target = self.get_expr(node.target)
    #     op = self.get_expr(node.op)
    #     self.assigning = True
    #     target = self.get_expr(node.target)
    #     self.assigning = False
    #     self.expression = target == op(old_target, value)

    def visit_Compare(self, node: ast.Compare) -> n.BinOp:
        left = self.visit(node.left)
        ops = map(self.visit, node.ops)
        comparators = map(self.visit, node.comparators)

        def combine(left: n.expr, zipped: Tuple[n.expr, n.expr]) -> n.expr:
            op, right = zipped
            return n.BinOp(left, cast(n.Operator, op), right)

        return cast(n.BinOp, reduce(combine, zip(ops, comparators), left))

    def visit_BoolOp(self, node: ast.BoolOp) -> n.BinOp:
        op = self.visit(node.op)
        value_list = [self.visit(v) for v in node.values]

        def combine(left: n.expr, right: n.expr) -> n.expr:
            return n.BinOp(left, op, right)

        return cast(n.BinOp, reduce(combine, value_list))

    def visit_Module(self, node: ast.Module) -> n.Module:
        return n.Module([self.visit(s) for s in node.body])

    def visit_Name(self, node: ast.Name) -> n.Name:
        idx = self.variables.get(node.id, VAR_START_VALUE)
        return n.Name(node.id, idx)

    # def visit_Call(self, node: ast.Call) -> n.Call:
    #     func = self.visit(node.func)

    def generic_visit(self, node: ast.AST) -> Any:
        print(f"visiting generically to {node}")
        if not isinstance(node, ast.AST):
            return node
        typename = type(node).__name__
        print("typename", typename)
        equivalent = getattr(n, typename, None)
        if equivalent is None:
            raise RuntimeError(
                f"Don't know what to do with a {typename} ({type(node)}); no such attribute exists"
            )
        fields = []
        for field in dataclasses.fields(equivalent):
            value = getattr(node, field.name)
            if isinstance(value, list):
                fields.append([self.visit(v) for v in value])
            else:
                fields.append(self.visit(value))
        return equivalent(*fields)
