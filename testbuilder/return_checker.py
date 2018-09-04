import ast
from typing import Sequence

class ReturnChecker(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.returns = False

    def visit_Return(self, node: ast.Return) -> None:
        self.returns = True

def contains_return(nodes: Sequence[ast.AST]) -> bool:
    checker = ReturnChecker()
    for node in nodes:
        checker.visit(node)
        if checker.returns:
            return checker.returns
    return checker.returns
