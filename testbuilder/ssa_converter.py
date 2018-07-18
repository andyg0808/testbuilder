import ast
from typing import Any, MutableMapping as MMapping, cast

VAR_START_VALUE = 0


def get_variable(name: str, idx: int) -> str:
    name = "pyname_" + name

    if idx == 0:
        return name
    else:
        return name + "_" + str(idx)


class SSAConverter(ast.NodeVisitor):
    def __init__(self, variables: MMapping[str, int]) -> None:
        super().__init__()
        self.variables = variables
        self.assigning = False

    def get_assign_name(self, name: str) -> str:
        idx = self.variables.get(name, VAR_START_VALUE)
        # If the node id is not in self.variables then we want to use 0 as
        # the initial value.
        if name in self.variables:
            idx += 1
        self.variables[name] = idx

        return self.get_name(name)

    def get_name(self, name: str) -> str:
        idx = self.variables.get(name, VAR_START_VALUE)
        return get_variable(name, idx)

    def visit_Name(self, node: ast.Name) -> ast.Name:
        return ast.Name(self.get_name(node.id), node.ctx)

    def visit_dest_name(self, node: ast.Name) -> ast.Name:
        return ast.Name(self.get_assign_name(node.id), node.ctx)

    def visit_Module(self, node: ast.Module) -> ast.Module:
        body = [self.visit(s) for s in node.body]
        return ast.Module(body)

    def visit_Expr(self, node: ast.Expr) -> ast.Expr:
        return ast.Expr(self.visit(node.value))

    def visit_Assign(self, node: ast.Assign) -> ast.Assign:
        # TODO: Support multiple assignment
        value = self.visit(node.value)
        targets = [self.visit_dest_name(cast(ast.Name, node.targets[0]))]
        return ast.Assign(targets, value)

    def generic_visit(self, node: ast.AST) -> Any:
        return node
