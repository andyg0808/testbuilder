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

    def generic_visit(self, obj: A, ignore=set()) -> Variator[A]:  # noqa: B006
        field_names = getattr(obj, "_fields", None)
        if field_names is None:
            # This is not an AST object
            return obj
        fields = set(obj._fields) - ignore
        for field in fields:
            yield from self.rebuilds(self.dispatch, obj, field)

    def dispatch(self, obj: A) -> Variator[A]:
        if type(obj) is list:
            if obj and isinstance(obj[0], ast.stmt):
                visitor = self.stmt_list_visit
            else:
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

    def visit_If(self, stmt: ast.If) -> Variator[ast.If]:
        yield from self.generic_visit(stmt, {"test"})
        if stmt.orelse:
            # Don't drop orelse if it's not present in the first place.
            # That's not going to change anything
            yield self.rebuild(stmt, orelse=[])
        yield from self.rebuilds(self.visit_conditional, stmt, "test")

    def visit_While(self, stmt: ast.While) -> Variator[ast.While]:
        yield from self.generic_visit(stmt, {"test"})
        if stmt.orelse:
            yield self.rebuild(stmt, orelse=[])
        yield from self.rebuilds(self.visit_conditional, stmt, "test")

    def visit_For(self, stmt: ast.For) -> Variator[ast.For]:
        yield from self.generic_visit(stmt)
        if stmt.orelse:
            yield self.rebuild(stmt, orelse=[])
        if isinstance(stmt.iter, ast.Call):
            yield from self.rebuilds(self.visit_call, stmt, "iter")
        cycle_call = ast.fix_missing_locations(
            ast.copy_location(
                ast.Call(
                    ast.Name(id="repeat", ctx=ast.Load()), args=[stmt.iter], keywords=[]
                ),
                stmt.iter,
            )
        )
        rebuilt = self.rebuild(stmt, iter=cycle_call)
        yield rebuilt

    def visit_call(self, call: ast.Call) -> Variator[ast.Call]:
        if isinstance(call.func, ast.Name):
            if call.func.id == "range":
                if len(call.args) > 1:
                    start = call.args[0]
                else:
                    start = 0
                yield self.rebuild(
                    call, func=self.rebuild(call.func, id="count"), args=[start]
                )
                yield self.rebuild(
                    call, func=self.rebuild(call.func, id="repeat"), args=[start]
                )

    def visit_conditional(self, op: ast.expr) -> Variator[ast.expr]:
        yield from self.visit(op)
        yield ast.copy_location(ast.NameConstant(True), op)
        yield ast.copy_location(ast.NameConstant(False), op)

    def stmt_list_visit(self, stmt_lst: List[ast.stmt]) -> Variator[List[ast.stmt]]:
        if len(stmt_lst) > 0:
            item = stmt_lst[0]
            for lst in self.list_visit(stmt_lst):
                if len(lst) == 0:
                    lst = self.empty(item)
                yield lst
        else:
            yield lst
