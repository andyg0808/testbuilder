import ast
from functools import reduce
from typing import Any, List, cast


class Formatter(ast.NodeVisitor):
    def visit_Assign(self, node: ast.Assign) -> str:
        targets = ", ".join(self.visit(t) for t in node.targets)
        return "{} = {}\n".format(targets, self.visit(node.value))

    def visit_AugAssign(self, node: ast.AugAssign) -> str:
        target = self.visit(node.target)
        op = self.visit(node.op)
        value = self.visit(node.value)
        return "{} {}= {}\n".format(target, op, value)

    def visit_Return(self, node: ast.Return) -> str:
        if node.value:
            return "return {}".format(self.visit(node.value))
        else:
            return "return"

    def visit_Expr(self, node: ast.Expr) -> str:
        return self.visit(node.value) + "\n"

    def visit_BinOp(self, node: ast.BinOp) -> str:
        left = self.visit(node.left)
        right = self.visit(node.right)
        op = self.visit(node.op)
        return "{} {} {}".format(left, op, right)

    def visit_Compare(self, node: ast.Compare) -> str:
        left = self.visit(node.left)
        ops = [self.visit(op) for op in node.ops]
        comparators = [self.visit(comp) for comp in node.comparators]
        op_comps = reduce(
            lambda prev, pair: prev + " {} {}".format(*pair), zip(ops, comparators), ""
        )
        return left + op_comps

    def visit_Name(self, node: ast.Name) -> str:
        return node.id

    def visit_Num(self, node: ast.Num) -> str:
        return str(node.n)

    def visit_Add(self, node: ast.Add) -> str:
        return "+"

    def visit_Sub(self, node: ast.Sub) -> str:
        return "-"

    def visit_Lt(self, node: ast.Lt) -> str:
        return "<"

    def visit_Gt(self, node: ast.Gt) -> str:
        return ">"

    def generic_visit(self, node: ast.AST) -> Any:
        return str(node) + ";\n"

    def visit(self, node: ast.AST) -> str:
        return cast(str, super().visit(node))


def format_tree(tree: ast.AST) -> str:
    f = Formatter()
    return f.visit(tree).strip()
