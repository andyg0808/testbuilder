import ast
from typing import MutableMapping as MMapping, List


class LineMapper(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.mapping: MMapping[int, List[ast.AST]] = {}
        self.current_nodes: List[ast.AST] = []
        self.nodeends: MMapping[ast.AST, int] = {}

    def generic_visit(self, node: ast.AST) -> None:
        self.current_nodes.append(node)
        lineno = getattr(node, 'lineno', None)
        if lineno is not None:
            for n in self.current_nodes:
                if self.nodeends.get(n, -1) < lineno:
                    self.nodeends[n] = lineno
            if lineno not in self.mapping:
                self.mapping[lineno] = self.current_nodes[:]
        super().generic_visit(node)
        self.current_nodes.pop()
