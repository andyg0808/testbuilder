import ast
import re
from abc import ABC
from typing import List

from logbook import Logger

from dataclasses import dataclass

ActionMarker = re.compile(r"# ([A-Z]+)/([A-Z]+): (.*)")
log = Logger("preprocessor")


class Preprocessor:
    def __init__(self, text: str) -> None:
        self.commands: List[ast.NodeTransformer] = []
        for line in text.splitlines():
            match = ActionMarker.fullmatch(line)
            print("match", line, match)
            if match is not None:
                log.info(
                    f"Found rewrite line requesting {match[1]}({match[2]}({match[3]}))"
                )
                node = Nodefinders.get(match[1], None)
                if node is None:
                    log.warn(f"Could not find nodefinder {match[1]}. Ignoring...")
                    continue
                action = Actions.get(match[2], None)
                if action is None:
                    log.warn(f"Could not find action {match[2]}. Ignoring...")
                    continue
                self.commands.append(node(action(match[3])))

    def __call__(self, tree: ast.AST) -> ast.AST:
        for command in self.commands:
            tree = command.visit(tree)
        return tree


@dataclass
class Attr(ast.NodeTransformer):
    transformer: ast.NodeTransformer

    def visit_Attribute(self, attr: ast.Attribute) -> ast.Attribute:
        return self.transformer.visit(attr)  # type: ignore


@dataclass
class AttrName(ast.NodeTransformer):
    transformer: ast.NodeTransformer

    def visit_Attribute(self, attr: ast.Attribute) -> ast.Attribute:
        new_attr = self.transformer.visit_String(attr.attr)  # type: ignore
        return ast.copy_location(  # type: ignore
            ast.Attribute(attr.value, new_attr), attr
        )


@dataclass
class Name(ast.NodeTransformer):
    transformer: ast.NodeTransformer

    def visit_Name(self, name: ast.Name) -> ast.Name:
        return self.transformer.visit(name)  # type: ignore


class Rename(ast.NodeTransformer):
    def __init__(self, action: str) -> None:
        self.search, self.replace = re.split(r"\s*->\s*", action)

    def visit_Name(self, name: ast.Name) -> ast.Name:
        return ast.copy_location(  # type: ignore
            ast.Name(self.visit_String(name.id)), name
        )

    def visit_String(self, string: str) -> str:
        return re.sub(self.search, self.replace, string)


Nodefinders = {"ATTR": Attr, "ATTRNAME": AttrName, "NAME": Name}
Actions = {"RENAME": Rename}
