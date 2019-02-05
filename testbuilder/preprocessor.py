import ast
import re
from abc import ABC
from typing import List, Tuple, cast

from logbook import Logger

from dataclasses import dataclass

ActionMarker = re.compile(r"# ([A-Z]+)/([A-Z]+): (.*)")
CommentLine = re.compile(r"\s*#|^\s*$")
log = Logger("preprocessor")

ChangeList = List[Tuple[str, str, str]]


class Preprocessor:
    def __init__(self, text: str) -> None:
        self.commands: List[ast.NodeTransformer] = []
        for line in text.splitlines():
            match = ActionMarker.fullmatch(line)
            print("match", line, match)
            if match is not None:
                self.add_rewrite_rule(match[1], match[2], match[3])
            elif not CommentLine.match(line):
                break

    def add_rewrite_rule(self, node: str, action: str, args: str) -> None:
        log.info(f"Adding rewrite rule {node}({action}({args}))")
        node_f = Nodefinders.get(node, None)
        if node_f is None:
            log.warn(f"Could not find nodefinder {node}.")
            raise MissingRewrite()
        action_f = Actions.get(action, None)
        if action_f is None:
            log.warn(f"Could not find action {action}.")
            raise MissingRewrite()
        self.commands.append(node_f(action_f(args)))

    def __call__(self, tree: ast.AST) -> ast.AST:
        for command in self.commands:
            tree = command.visit(tree)
        return tree


class AutoPreprocessor(Preprocessor):
    def __init__(self, text: str, changes: List[Tuple[str, str, str]]) -> None:
        super().__init__(text)

        for change in changes:
            self.add_rewrite_rule(*change)


class MissingRewrite(RuntimeError):
    pass


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
        return cast(
            ast.Attribute, ast.copy_location(ast.Attribute(attr.value, new_attr), attr)
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
        return cast(
            ast.Name, ast.copy_location(ast.Name(self.visit_String(name.id)), name)
        )

    def visit_String(self, string: str) -> str:
        return re.sub(self.search, self.replace, string)


Nodefinders = {"ATTR": Attr, "ATTRNAME": AttrName, "NAME": Name}
Actions = {"RENAME": Rename}
