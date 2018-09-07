import dataclasses
import inspect
import re
import traceback
from abc import abstractmethod
from typing import (
    Any,
    Callable,
    Generator,
    Generic,
    Iterator,
    List,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    Type,
    TypeVar,
    Union,
    cast,
)

from logbook import Logger
from toolz import mapcat

log = Logger("visitor")


# Generic types for visitors derived from
# http://logji.blogspot.com/2012/02/correcting-visitor-pattern.html

A = TypeVar("A")
B = TypeVar("B")

Result = Union[Iterator[B], B]

NameRegex = re.compile(r"visit_[A-Z]")
SuggestionRegex = re.compile(r"visit", flags=re.IGNORECASE)


class VisitError(NotImplementedError):
    def __str__(self) -> str:
        msg = "Error from Visitor"
        if len(self.args) > 0:
            msg = f"No handler for {self.args[0]}."
        if len(self.args) > 1:
            msg += f"\nMaybe {self.args[1]} isn't capitalized correctly?"

        stack = traceback.extract_tb(self.__traceback__)
        filtered_stack = [s for s in stack if s.filename != __file__]
        if filtered_stack:
            caller = filtered_stack[-1]
            msg += f"\nError at line {caller.lineno} while running {caller.name}"
            msg += f"\nin {caller.filename}:"
            msg += f"\n  {caller.line}"

        return msg


class SimpleVisitor(Generic[B]):
    T = TypeVar("T")

    def __call__(self, v: Any, *args: Any) -> B:
        return self.visit(v, *args)

    def visit(self, v: Any, *args: Any) -> B:
        func = self.__find_function(v.__class__)
        return func(v, *args)

    def __find_function(self, start_class: Type) -> Callable[..., B]:
        cache = getattr(self, "__fun_cache", {})
        suggestion = None
        if start_class in cache:
            return cast(Callable[..., B], cache[start_class])
        for cls in inspect.getmro(start_class):
            func = self.__scan_functions(cls)
            if func is not None:
                cache[start_class] = func
                setattr(self, "__fun_cache", cache)
                return func
            elif suggestion is None:
                suggestions = getattr(self, "__suggestions", {})
                log.debug("suggestions", suggestions)
                suggestion = suggestions.get(cls, None)
        if suggestion is not None:
            raise VisitError(start_class, suggestion)
        else:
            raise VisitError(start_class)

    def __scan_functions(self, target_class: Type) -> Callable[..., B]:
        typecache = getattr(self, "__type_cache", None)
        if typecache is None:
            typecache = {}
            suggestions = {}
            # See https://stackoverflow.com/a/1911287/
            for name, method in inspect.getmembers(self, inspect.ismethod):
                signature = inspect.signature(method)
                if len(signature.parameters) < 1:
                    if SuggestionRegex.match(name):
                        log.warn(f"Found {name} with too few parameters")
                    continue
                parameters = list(signature.parameters.values())
                param = parameters[0]
                if NameRegex.match(name):
                    typecache[param.annotation] = method
                elif SuggestionRegex.match(name):
                    log.debug("found suggestion", name)
                    suggestions[param.annotation] = name
                else:
                    log.debug("not suggesting", name)

            setattr(self, "__type_cache", typecache)
            setattr(self, "__suggestions", suggestions)
        return cast(Callable[..., B], typecache.get(target_class, None))


class GenericVisitor(SimpleVisitor[A]):
    def visit(self, v: Any, *args: Any) -> A:
        try:
            return super().visit(v, *args)
        except VisitError:
            # If we get a VisitError, fall through to using the
            # `generic_visit` function. Trying to call `generic_visit`
            # here causes later, genuine VisitErrors to be caused
            # during handling of this VisitError. We want them to be
            # independent---this error is completely dealt with after
            # this line (because `generic_visit` is the correct action
            # to take when a specialized function is missing).
            pass
        return self.generic_visit(v, *args)


    @abstractmethod
    def generic_visit(self, v: Any, *args: Any) -> A:
        ...


class SearchVisitor(GenericVisitor[Optional[A]]):
    def generic_visit(self, v: Any, *args: Any) -> Optional[A]:
        try:
            fields = dataclasses.fields(v)
        except TypeError:
            return None
        for f in fields:
            data = getattr(v, f.name)
            if isinstance(data, Sequence):
                for d in data:
                    res = self.visit(d, *args)
                    if res is not None:
                        return res
            else:
                res = self.visit(data, *args)
                if res is not None:
                    return res
        return None


class GatherVisitor(GenericVisitor[List[A]]):
    def generic_visit(self, v: Any, *args: Any) -> List[A]:
        def arg_visit(v: Any) -> List[A]:
            return self.visit(v, *args)

        try:
            fields = dataclasses.fields(v)
        except TypeError:
            # If we are trying to look for fields on something
            # that isn't a dataclass, it's probably a primitive
            # field type, so just stop here.
            return []
        results: List[A] = []
        for f in fields:
            data = getattr(v, f.name)
            if isinstance(data, Sequence):
                results += mapcat(arg_visit, data)
            else:
                results += arg_visit(data)
        return results


class CoroutineVisitor(GenericVisitor[Generator[A, B, None]]):
    def generic_visit(self, v: Any, *args: Any) -> Generator[A, B, None]:
        def arg_visit(v: Any) -> Generator[A, B, None]:
            return self.visit(v, *args)

        try:
            fields = dataclasses.fields(v)
        except TypeError:
            return
        for f in fields:
            data = getattr(v, f.name)
            if isinstance(data, Sequence):
                for d in data:
                    yield from arg_visit(d)
            else:
                yield from arg_visit(data)
        return


class UpdateVisitor(GenericVisitor):
    def __init__(self) -> None:
        self.visited_nodes: MMapping[int, Any] = {}

    def visit(self, v: A, *args: Any) -> A:
        # Use already-visited object if it exists.
        # This makes handling trees with joins well-behaved.
        if self.id(v) in self.visited_nodes:
            return self.get_updated(v)
        visited = super().visit(v, *args)
        self.visited_nodes[self.id(v)] = visited
        return cast(A, visited)

    def get_updated(self, original: A) -> A:
        return cast(A, self.visited_nodes[self.id(original)])

    def id(self, obj: Any) -> Any:
        """
        Returns a unique identifier for a node. Can be overridden to
        modify the notion of equivalence.
        """
        return id(obj)

    def generic_visit(self, v: A, *args: Any) -> A:
        try:
            fields = dataclasses.fields(v)
        except TypeError as err:
            # If we are trying to look for fields on something
            # that isn't a dataclass, it's probably a primitive
            # field type, so just stop here.
            return v
        results: MMapping[str, Any] = {}
        for f in fields:
            if f.name.startswith("_"):
                continue
            data = getattr(v, f.name)
            res: Any
            if isinstance(data, list):
                res = [self.visit(x, *args) for x in data]
            else:
                res = self.visit(data, *args)
            results[f.name] = res
        return cast(A, v.__class__(**results))
