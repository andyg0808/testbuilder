import ast
from typing import List, Sequence


class _VarCollector(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.vars: List[str] = []

    def visit_Name(self, node: ast.Name) -> None:
        self.vars.append(node.id)

    def visit_Assign(self, node: ast.Assign) -> None:
        self.visit(node.value)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value is not None:
            self.visit(node.value)


class _TargetCollector(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.targets: List[str] = []

    def visit_Name(self, node: ast.Name) -> None:
        self.targets.append(node.id)

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            self.visit(target)

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        self.visit(node.target)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        self.visit(node.target)


def find_vars(elem: ast.AST) -> Sequence[str]:
    collector = _VarCollector()
    collector.visit(elem)
    return collector.vars


def find_targets(elem: ast.AST) -> Sequence[str]:
    collector = _TargetCollector()
    collector.visit(elem)
    return collector.targets
