import ast
from typing import MutableMapping as MMapping

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

    def visit_Name(self, node: ast.Name) -> ast.Name:
        return node
