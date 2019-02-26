import ast
from typing import (
    Any,
    Generator,
    Iterable,
    Iterator,
    List,
    Mapping,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    TypeVar,
)

from visitor import GenericVisitor

A = TypeVar("A", bound=ast.AST)

Variator = Generator[A, None, None]


class Mutator:
    def __init__(self, code: ast.AST) -> None:
        self.code = code

    def __iter__(self) -> Variator[A]:
        m = _MutationGenerator()
        for mutation in m.visit(self.code):
            try:
                glob = {}
                code = compile(mutation, "<mutation>", "exec")
                yield mutation
            except Exception as e:
                print("Caught exception", e)
                print("while compiling", ast.dump(mutation))


class _MutationGenerator(GenericVisitor):
    def rebuild(self, obj: A, **changes) -> A:
        fields = {f: getattr(obj, f) for f in obj._fields}
        fields.update(**changes)
        return obj.__class__(**fields)

    def generic_visit(self, obj: A) -> Variator[A]:
        field_names = getattr(obj, "_fields", None)
        if field_names is None:
            # This is not an AST object
            return obj
        fields = set(obj._fields)
        for field in fields:
            updated = {f: getattr(obj, f) for f in fields - {field}}
            for update in self.dispatch(getattr(obj, field)):
                updated[field] = update
                yield ast.copy_location(obj.__class__(**updated), obj)

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

    def visit_Cmpop(self, v: ast.cmpop) -> Variator[ast.cmpop]:
        options = {ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE}
        available = options - {type(v)}
        for op in available:
            yield ast.copy_location(op(), v)

    def dropout_list(self, lst: List[A]) -> Variator[List[A]]:
        for i in range(len(lst)):
            yield lst[:i] + lst[i + 1 :]

    # def visit_Module(self, v: ast.Module) -> Variator[ast.Module]:
    #     for droppedout in self.dropout_list(v.body):
    #         yield ast.Module(body=droppedout)
    #     for body in self.dispatch(v.body):
    #         yield ast.Module(body=body)
