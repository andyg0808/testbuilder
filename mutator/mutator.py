import ast
from typing import (
    Any,
    Callable,
    Generator,
    Iterable,
    Iterator,
    List,
    Mapping,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    TypeVar,
    Union,
)

from logbook import Logger

from visitor import GenericVisitor

log = Logger("mutator")
A = TypeVar("A", bound=ast.AST)
T = TypeVar("T")

Variator = Generator[A, None, None]


class Mutator:
    def __init__(self, code: ast.AST) -> None:
        self.code = code

    def __iter__(self) -> Variator[A]:
        m = _MutationGenerator()
        for mutation in m.visit(self.code):
            try:
                # If this compile fails, it means the mutation is not
                # valid Python. We throw out such mutations.
                compile(mutation, "<mutation>", "exec")
                yield mutation
            except Exception as e:
                dump = ast.dump(mutation)
                log.warn(f"Caught exception {e} while compiling {dump}")


class _MutationGenerator(GenericVisitor):
    def rebuild(self, obj: A, **changes) -> A:
        fields = {f: getattr(obj, f) for f in obj._fields}
        fields.update(changes)
        return ast.copy_location(obj.__class__(**fields), obj)

    def rebuilds(
        self, visitor: Callable[[T], Variator[T]], obj: A, key: str
    ) -> Variator[A]:
        """Yield `obj` rebuilt with every variant resulting from calling
        `visitor` on `obj`.`key`.

        """
        fields = set(obj._fields)
        updated = {f: getattr(obj, f) for f in fields - {key}}
        log.debug(f"Rebuilding {obj} on field {key} with {visitor}")
        for update in visitor(getattr(obj, key)):
            updated[key] = update
            yield ast.copy_location(obj.__class__(**updated), obj)

    def generic_visit(self, obj: A) -> Variator[A]:
        field_names = getattr(obj, "_fields", None)
        if field_names is None:
            # This is not an AST object
            return obj
        fields = set(obj._fields)
        for field in fields:
            yield from self.rebuilds(self.dispatch, obj, field)

    def dispatch(self, obj: A) -> Variator[A]:
        if type(obj) is list:
            visitor = self.list_visit
        else:
            visitor = self.visit
        yield from visitor(obj)

    def list_visit(self, lst: List[A]) -> Variator[List[A]]:
        yield from self.mutate_list(lst)
        yield from self.dropout_list(lst)

    def mutate_list(self, lst: List[A]) -> Variator[List[A]]:
        for i in range(len(lst)):
            first = lst[:i]
            last = lst[i + 1 :]
            changing = lst[i]
            for repl in self.dispatch(changing):
                yield first + [repl] + last

    # def visit_Cmpop(self, v: ast.cmpop) -> Variator[ast.cmpop]:
    #     options = {ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE}
    #     available = options - {type(v)}
    #     for op in available:
    #         yield ast.copy_location(op(), v)

    def dropout_list(self, lst: List[A]) -> Variator[List[A]]:
        if lst:
            for i in range(len(lst)):
                yield lst[:i] + lst[i + 1 :]

    def visit_BoolOp(
        self, op: ast.BoolOp
    ) -> Variator[Union[ast.BoolOp, ast.NameConstant]]:
        if len(op.values) > 2:
            yield from self.rebuilds(self.list_visit, op, "values")
        else:
            yield op.values[0]
            yield op.values[1]
            yield from self.rebuilds(self.mutate_list, op, "values")
        yield ast.copy_location(ast.NameConstant(True), op)
        yield ast.copy_location(ast.NameConstant(False), op)

    def empty(self, stmt: ast.stmt) -> List[ast.stmt]:
        return [ast.copy_location(ast.Pass(), stmt)]

    def stmt_list_visit(self, stmt: ast.stmt, field: str) -> Variator[List[ast.stmt]]:
        for lst in self.list_visit(getattr(stmt, field)):
            if len(lst) == 0:
                lst = self.empty(stmt)
            yield self.rebuild(stmt, **{field: lst})

    def visit_If(self, stmt: ast.If) -> Variator[ast.If]:
        # This one is not in the original paper
        if len(stmt.body) > 1:
            yield self.rebuild(stmt, body=self.empty(stmt))
        # Don't drop orelse if it's not present in the first place. That's not going to change anything
        if stmt.orelse:
            yield self.rebuild(stmt, orelse=[])
        yield from self.stmt_list_visit(stmt, "body")
        yield from self.rebuilds(self.list_visit, stmt, "orelse")
        yield from self.rebuilds(self.visit_conditional, stmt, "test")

    def visit_While(self, stmt: ast.While) -> Variator[ast.While]:
        if stmt.orelse:
            yield self.rebuild(stmt, orelse=[])
        yield from self.stmt_list_visit(stmt, "body")
        yield from self.rebuilds(self.visit_conditional, stmt, "test")

    def visit_conditional(self, op: ast.expr) -> Variator[ast.expr]:
        yield from self.visit(op)
        yield ast.copy_location(ast.NameConstant(True), op)
        yield ast.copy_location(ast.NameConstant(False), op)

    def visit_FunctionDef(self, func: ast.FunctionDef) -> Variator[ast.FunctionDef]:
        yield from self.rebuilds(self.visit, func, "args")
        yield from self.stmt_list_visit(func, "body")
        yield from self.rebuilds(self.list_visit, func, "decorator_list")
        yield from self.rebuilds(self.visit, func, "returns")
