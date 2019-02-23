import ast
import re
from typing import List, Tuple, Union

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
            log.debug("match {} {}", line, match)
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
class NodeFinder(ast.NodeTransformer):
    transformer: ast.NodeTransformer


class Attr(NodeFinder):
    def visit_Attribute(self, attr: ast.Attribute) -> ast.Attribute:
        return self.transformer.visit(attr)  # type: ignore


class AttrName(NodeFinder):
    def visit_Attribute(self, attr: ast.Attribute) -> ast.Attribute:
        new_attr = self.transformer.visit_String(attr.attr)  # type: ignore
        return ast.copy_location(ast.Attribute(attr.value, new_attr), attr)


class Subscript(NodeFinder):
    def visit_Subscript(self, sub: ast.Subscript) -> ast.AST:
        return self.transformer.visit(sub)  # type: ignore


class Name(NodeFinder):
    def visit_Name(self, name: ast.Name) -> ast.Name:
        return self.transformer.visit(name)  # type: ignore


class TupleFinder(NodeFinder):
    def visit_Tuple(self, tup: ast.Tuple) -> ast.AST:
        return self.transformer.visit(tup)  # type: ignore


class Action(ast.NodeTransformer):
    def __init__(self, action: str) -> None:
        self.action = action
        if len(action) > 2:
            self.search, self.replace = re.split(r"\s*->\s*", action)


class Rename(Action):
    def visit_Name(self, name: ast.Name) -> ast.Name:
        return ast.copy_location(ast.Name(self.visit_String(name.id)), name)

    def visit_String(self, string: str) -> str:
        return re.sub(self.search, self.replace, string)


class Parify(Action):
    def visit_Subscript(
        self, sub: ast.Subscript
    ) -> Union[ast.Attribute, ast.Subscript]:
        if isinstance(sub.slice, ast.Index):
            index = sub.slice.value
            if isinstance(index, ast.Num):
                if index.n == int(self.search):
                    return ast.copy_location(
                        ast.Attribute(sub.value, self.replace), sub
                    )
        return sub

    def visit_Tuple(self, tup: ast.Tuple) -> Union[ast.Tuple, ast.Call]:
        if len(tup.elts) == 2:
            pair = ast.copy_location(ast.Name("Pair"), tup)
            return ast.copy_location(ast.Call(pair, tup.elts, []), tup)
        return tup


Nodefinders = {
    "ATTR": Attr,
    "ATTRNAME": AttrName,
    "NAME": Name,
    "SUBSCRIPT": Subscript,
    "TUPLE": TupleFinder,
}
Actions = {"RENAME": Rename, "PARIFY": Parify}
