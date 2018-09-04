from . import nodetree as n
from .visitor import SimpleVisitor


class SSAVisitor(SimpleVisitor[str]):
    def visit_Return(self, node: n.Return) -> str:
        if node.value:
            return "return {}".format(self.visit(node.value))
        else:
            return "return"

    def visit_Expr(self, node: n.Expr) -> str:
        return self.visit(node.value) + "\n"

    def visit_BinOp(self, node: n.BinOp) -> str:
        left = self.visit(node.left)
        right = self.visit(node.right)
        op = self.visit(node.op)
        return f"{left} {op} {right}"

    def visit_Name(self, node: n.Name) -> str:
        return f"${node.id}_{node.set_count}"

    def visit_Int(self, node: n.Int) -> str:
        return str(node.v)

    def visit_Float(self, node: n.Float) -> str:
        return str(node.v)

    def visit_Add(self, node: n.Add) -> str:
        return "+"

    def visit_Sub(self, node: n.Sub) -> str:
        return "-"

    def visit_Lt(self, node: n.Lt) -> str:
        return "<"

    def visit_Gt(self, node: n.Gt) -> str:
        return ">"

    def visit_Eq(self, node: n.Eq) -> str:
        return "=="

    def visit_Set(self, node: n.Set) -> str:
        target = self.visit(node.target)
        expr = self.visit(node.e)
        return f"{target} ← {expr}"

    def visit_Str(self, node: n.Str) -> str:
        return f"'{node.s}'"


def format_tree(node: n.Node) -> str:
    v = SSAVisitor()
    return v.visit(node)
