#!/usr/bin/env python3
import ast
from copy import copy
from abc import abstractmethod
from functools import reduce
from typing import (
    Any,
    Generic,
    List,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    Set,
    TypeVar,
    Union,
    cast,
)

from .linemapper import LineMapper
from .var_collector import find_targets, find_vars

T = TypeVar("T")

DependencyTree = List[Union["Dependency[T]", "DependencyTree"]]  # type: ignore

Linenumbered = Union[ast.expr, ast.stmt]

Conditioned = Union[ast.If, ast.While]


class Dependency(Generic[T]):
    def __init__(self, dependencies: Set["Dependency"], code: T, lineno: int) -> None:
        self.dependencies: Set["Dependency"] = dependencies
        self.code = code
        self.lineno: int = lineno
        self.required = False

    def __str__(self) -> str:
        return "{}\uf061 {}".format(self.lineno, self.code)

    def __repr__(self) -> str:
        return "{}({},{},{})".format(
            self.__class__.__name__,
            [getattr(i, "lineno", i) for i in self.dependencies],
            self.format_code(),
            self.lineno,
        )

    @abstractmethod
    def format_code(self) -> str:
        return repr(self.code)

    def dep_tree(self, done: Optional[Set[Any]] = None) -> List[str]:
        if not done:
            done = set()

        output: List[str] = []
        if self not in done:
            output.append('{}[label="{}"];'.format(id(self), self.lineno))
            done.add(self)
        for dep in self.dependencies:
            output += dep.dep_tree(done)
            link = "{} -> {};".format(id(self), id(dep))
            if link not in done:
                output.append(link)
                done.add(link)

        return output

    def format_slice(self) -> List["Dependency"]:
        descr = [self]
        added = set(descr)
        for dep in self.dependencies:
            for i in dep.format_slice():
                if i not in added:
                    descr.append(i)
                    added.add(i)
        return descr

    def linearize(self) -> List["Dependency"]:
        deps = self.format_slice()
        deps.sort(key=lambda d: d.lineno)
        return deps

    def walk_tree(self) -> DependencyTree:
        return [self] + [i.walk_tree() for i in self.dependencies]  # type: ignore


class Variable(Dependency[str]):
    """
    Stores a variable passed into a function.
    """

    def __init__(self, varname: str, lineno: int) -> None:
        super().__init__(set(), varname, lineno)

    def dep_tree(self, done: Optional[Set[Any]] = None) -> List[str]:
        if not done:
            done = set()

        if self not in done:
            done.add(self)
            return ['{}[label="{}"];'.format(id(self), self.code)]
        else:
            return []

    def format_code(self) -> str:
        return self.code

    def __eq__(self, o: Any) -> bool:
        if hasattr(o, "code"):
            if self.code == o.code:
                if hasattr(o, "lineno"):
                    if self.lineno == o.lineno:
                        return True
        return False

    def __repr__(self) -> str:
        return "{}({},{})".format(self.__class__.__name__, self.code, self.lineno)

    def __hash__(self) -> int:
        return hash(self.code) + hash(self.lineno)


class Statement(Dependency[ast.stmt]):
    def __init__(
        self,
        dependencies: Set[Dependency],
        code: ast.stmt,
        conditional: Sequence["Conditional"],
    ) -> None:
        super().__init__(dependencies, code, code.lineno)
        self.conditional: Sequence["Conditional"] = conditional

    def format_code(self) -> str:
        return ast.dump(self.code, annotate_fields=False)

    def __repr__(self) -> str:
        if self.conditional:
            return "{}({},{},{},conditional={})".format(
                self.__class__.__name__,
                [getattr(i, "lineno", i) for i in self.dependencies],
                self.format_code(),
                self.lineno,
                repr(self.conditional),
            )
        else:
            return "{}({},{},{})".format(
                self.__class__.__name__,
                [getattr(i, "lineno", i) for i in self.dependencies],
                self.format_code(),
                self.lineno,
            )


class Conditional(Statement):
    """
    Stores a conditional which controls the things which depend on it.
    """

    def neg(self) -> "Conditional":
        return NegConditional(self.dependencies, self.code, self.conditional)


class NegConditional(Conditional):
    """
    Tagging class for negated conditionals: when the falsity of a conditional
    controls the dependent lines
    """

    def neg(self) -> Conditional:
        return Conditional(self.dependencies, self.code, self.conditional)


class SliceVisitor(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.stop = False
        self.variables: MMapping[str, Set[Dependency]] = {}
        self.lines: MMapping[int, Statement] = {}
        self.last_var: Optional[Dependency] = None
        self.conds: List[Conditional] = []
        self.return_triggers: Set[Conditional] = set()

    def visit_Assign(self, node: ast.Assign) -> None:
        self.generic_visit(node)
        for var in find_targets(node):
            if self.last_var is not None:
                self.variables[var] = {self.last_var}

    def visit_single_assignment(self, node: Union[ast.AugAssign, ast.AnnAssign]) -> None:
        self.generic_visit(node)
        var = find_targets(node.target)[0]
        if self.last_var is not None:
            self.variables[var] = {self.last_var}

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        self.visit_single_assignment(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        # Only include node if it actually is doing an assignment
        if node.value is not None:
            self.visit_single_assignment(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        args = node.args
        for v in args.args:
            self._store_varname(v.arg, node.lineno)

        self.visit_list(node.body)

    def visit_list(self, body: Sequence[ast.AST]) -> None:
        try:
            for l in body:
                self.visit(l)
        except FoundReturn:
            pass

    def _store_varname(self, varname: str, lineno: int) -> Set[Dependency]:
        # TODO I think this function should be split into two, one which is
        # used when the variable should exist and one to create a variable.
        # Unless maybe it's this way because we want to support slicing code
        # snippets which don't have all their required variables defined.

        if varname not in self.variables:
            val: Set[Dependency[str]] = {Variable(varname, lineno)}
            self.variables[varname] = val
        else:
            val = self.variables[varname]
        return val

    def visit_Name(self, node: ast.Name) -> None:
        self._store_varname(node.id, node.lineno)

    def get_deps(self, node: Linenumbered) -> Set[Dependency]:
        """
        Finds all variables in an expression and returns Dependency instances
        for all of them (possibly along with the dependencies specified in
            self.conds).
        """
        lst: Set[Dependency] = set()
        for var in find_vars(node):
            lst |= self._store_varname(var, node.lineno)
        return lst.union(self.conds).union(self.return_triggers)

    def get_conds(self) -> Sequence["Conditional"]:
        return copy(self.conds)

    def visit_If(self, node: ast.If) -> None:
        self._visit_a_Conditioned(node)

    def _visit_a_Conditioned(self, node: Conditioned) -> None:
        deps = self.get_deps(node.test)
        expr = ast.Expr(node.test, lineno=node.lineno, col_offset=node.col_offset)
        cond = Conditional(deps, expr, self.get_conds())

        self.lines[node.lineno] = cond

        origvars = copy(self.variables)
        origtriggers = copy(self.return_triggers)

        self.conds.append(cond)
        self.visit_list(node.body)
        self.conds.pop()

        truevars = copy(self.variables)
        truetriggers = copy(self.return_triggers)

        self.return_triggers = origtriggers
        self.variables = origvars

        self.conds.append(cond.neg())
        self.visit_list(node.orelse)
        self.conds.pop()
        falsevars = copy(self.variables)

        self.return_triggers |= truetriggers

        vars: MMapping[str, Set[Dependency]] = {}
        for k in truevars.keys() | falsevars.keys():
            vars[k] = truevars.get(k, set()) | falsevars.get(k, set())
        self.variables = vars

    def visit_While(self, node: ast.While) -> None:
        self._visit_a_Conditioned(node)

    def generic_visit(self, node: ast.AST) -> None:
        if isinstance(node, ast.stmt):
            deps = self.get_deps(node)
            self.last_var = Statement(deps, node, self.get_conds())
            # This isn't linked to the actual variable if it's not an existing
            # var

            if hasattr(node, "lineno"):
                self.lines[node.lineno] = self.last_var

        super().generic_visit(node)

    def visit_Module(self, node: ast.Module) -> None:
        self.visit_list(node.body)

    def visit_Return(self, node: ast.Return) -> None:
        self.generic_visit(node)
        # We don't care about the details of these trigger values; they're just
        # going to be dumped in self.conds for future lines.
        self.return_triggers.update(self.conds)
        raise FoundReturn()


class Slicer:
    def __init__(self, code: ast.AST) -> None:
        self.slicer = SliceVisitor()
        self.slicer.visit(code)

    def lines(self) -> List[int]:
        return sorted(list(self.slicer.lines.keys()))

    def statements(self) -> List[Statement]:
        stmts = []
        for line in self.lines():
            value = self.slicer.lines[line]
            if type(value) == Statement:
                dep = self.make_slice(value)
                stmts.append(cast(Statement, dep))
        return stmts

    def make_slice(self, value: Dependency) -> Dependency:
        sliced = copy(value)
        sliced.required = True
        return sliced

    def _get_lineno(self, lineno: Any) -> Any:
        if lineno == -1:
            return max(self.slicer.lines.keys())
        else:
            return lineno

    def __contains__(self, lineno: object) -> bool:
        """
        Check if a given line number has a slice available.
        """
        return self._get_lineno(lineno) in self.slicer.lines

    def take_slice(self, lineno: int, filename: Optional[str] = None) -> Dependency:
        lineno = self._get_lineno(lineno)
        sliced = self.make_slice(self.slicer.lines[lineno])
        if filename:
            with open(filename, "w") as f:
                data = "\n".join(sliced.dep_tree())
                formatted = """
    digraph G {{
    {}
    }}
                """.format(
                    data
                )
                f.write(formatted)

        return sliced


def take_slice(
    code: ast.AST, line: int, filename: Optional[str] = None
) -> Optional[Dependency]:
    s = Slicer(code)
    if line in s:
        return s.take_slice(line, filename)
    else:
        return None


class FoundReturn(Exception):
    pass
