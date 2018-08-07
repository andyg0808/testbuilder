import ast
from typing import Iterator, List


class FunctionWalker(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.functions: List[ast.FunctionDef] = []

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self.functions.append(node)

    def __iter__(self) -> Iterator[ast.FunctionDef]:
        return iter(self.functions)

    def __getitem__(self, idx: int) -> ast.FunctionDef:
        return self.functions[idx]


def split_functions(tree: ast.AST) -> Iterator[ast.FunctionDef]:
    walker = FunctionWalker()
    walker.visit(tree)
    return iter(walker)
