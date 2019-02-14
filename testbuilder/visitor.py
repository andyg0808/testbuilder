import inspect
import re
import traceback
import typing
from abc import abstractmethod
from typing import (
    Any,
    Callable,
    Generator,
    Generic,
    Iterator,
    Mapping,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    Set,
    Type,
    TypeVar,
    Union,
    cast,
    get_type_hints,
)

from logbook import Logger

import dataclasses

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

    def __call__(self, v: Any, *args: Any, **kwargs: Any) -> B:
        return self.visit(v, *args, **kwargs)

    def visit(self, v: Any, *args: Any, **kwargs: Any) -> B:
        func = self.__find_function(v.__class__)
        return func(v, *args, **kwargs)

    def __find_function(self, start_class: Type[T]) -> Callable[..., B]:
        cache = getattr(self, "__fun_cache", {})
        errs = getattr(self, "__err_cache", {})
        suggestion = None
        if start_class in cache:
            return cast(Callable[..., B], cache[start_class])
        if start_class in errs:
            raise VisitError(*errs[start_class])
        if __debug__:
            log.trace("Finding functions in {}", type(self))
        for cls in inspect.getmro(start_class):
            func = self.__scan_functions(cls)
            if func is not None:
                cache[start_class] = func
                setattr(self, "__fun_cache", cache)
                if __debug__:
                    log.trace(f"Found function {func}")
                return func
            elif suggestion is None:
                suggestions = getattr(self.__class__, "__suggestions", {})
                suggestion = suggestions.get(cls, None)
        if suggestion is not None:
            errs[start_class] = (start_class, suggestion)
        else:
            errs[start_class] = (start_class,)
        setattr(self, "__err_cache", errs)
        raise VisitError(*errs[start_class])

    def __scan_functions(self, target_class: Type[T]) -> Callable[..., B]:
        typecache = getattr(self.__class__, "__type_cache", None)
        if typecache is None:
            typecache = {}
            suggestions = {}
            # See https://stackoverflow.com/a/1911287/
            for name, method in inspect.getmembers(self, inspect.ismethod):
                signature = inspect.signature(method)
                annotations = get_type_hints(method)
                if len(signature.parameters) < 1:
                    if SuggestionRegex.match(name):
                        log.warn(f"Found {name} with too few parameters")
                    continue
                parameters = list(signature.parameters.values())
                param = parameters[0]
                if NameRegex.match(name):
                    annotation = annotations[param.name]
                    # This next line is bad, but we want to try to
                    # detect and handle generics by looking at their
                    # base class.
                    if isinstance(annotation, typing._GenericAlias):  # type: ignore
                        annotation = annotation.__origin__
                    if __debug__:
                        log.debug("Found visitor {} for {}", name, annotation)
                    typecache[annotation] = name
                elif SuggestionRegex.match(name):
                    if __debug__:
                        log.debug("Found suggestion {}", name)
                    suggestions[annotations[param.name]] = name
                else:
                    if __debug__:
                        log.debug("Ignoring {}", name)

            setattr(self.__class__, "__type_cache", typecache)
            setattr(self.__class__, "__suggestions", suggestions)
        name = typecache.get(target_class)
        if name is None:
            return None
        return cast(Optional[Callable[..., B]], getattr(self, name))


class GenericVisitor(SimpleVisitor[A]):
    def visit(self, v: Any, *args: Any, **kwargs: Any) -> A:
        try:
            return super().visit(v, *args, **kwargs)
        except VisitError as err:
            if __debug__:
                log.debug(
                    "VisitError received; visiting generically [Error is {}]", err
                )
            # If we get a VisitError, fall through to using the
            # `generic_visit` function. Trying to call `generic_visit`
            # here causes later, genuine VisitErrors to be caused
            # during handling of this VisitError. We want them to be
            # independent---this error is completely dealt with after
            # this line (because `generic_visit` is the correct action
            # to take when a specialized function is missing).
            pass
        return self.generic_visit(v, *args, **kwargs)

    @abstractmethod
    def generic_visit(self, v: Any, *args: Any, **kwargs: Any) -> A:
        ...


class CacheVisitor:
    CACHE_ATTR = "__generic_cache"

    def cacheclear(self) -> None:
        cache = getattr(self, CacheVisitor.CACHE_ATTR, None)
        if cache is not None:
            cache.clear()

    def cacheget(self, v: Any) -> A:
        cache = getattr(self, CacheVisitor.CACHE_ATTR, {})
        return cast(A, cache.get(id(v), None))

    def cacheput(self, v: Any, val: A) -> None:
        cache = getattr(self, CacheVisitor.CACHE_ATTR, None)
        if cache is None:
            setattr(self, CacheVisitor.CACHE_ATTR, {id(v): val})
        else:
            cache[id(v)] = val

    def cachedrop(self, v: Any) -> None:
        cache = getattr(self, CacheVisitor.CACHE_ATTR, None)
        if cache is not None:
            del cache[id(v)]


class SearchVisitor(GenericVisitor[Optional[A]]):
    def generic_visit(self, v: Any, *args: Any, **kwargs: Any) -> Optional[A]:
        try:
            fields = dataclasses.fields(v)
        except TypeError:
            return None
        for f in fields:
            data = getattr(v, f.name)
            if isinstance(data, Sequence):
                for d in data:
                    res = self.visit(d, *args, **kwargs)
                    if res is not None:
                        return res
            if isinstance(data, Mapping):
                for v in data.values():
                    res = self.visit(v, *args, **kwargs)
                    if res is not None:
                        return res
            else:
                res = self.visit(data, *args, **kwargs)
                if res is not None:
                    return res
        return None


class SetGatherVisitor(GenericVisitor[Set[A]], CacheVisitor):
    def visit(self, v: Any, *args: Any, **kwargs: Any) -> Set[A]:
        val: Optional[Set[A]] = self.cacheget(v)
        if val is not None:
            return val
        val = set()
        self.cacheput(v, val)
        res = super().visit(v, *args, **kwargs)
        val |= res
        return val

    def generic_visit(self, v: Any, *args: Any, **kwargs: Any) -> Set[A]:
        def arg_visit(v: Any) -> Set[A]:
            return self.visit(v, *args, **kwargs)

        try:
            fields = dataclasses.fields(v)
        except TypeError:
            # If we are trying to look for fields on something
            # that isn't a dataclass, it's probably a primitive
            # field type, so just stop here.
            return set()
        results: Set[A] = set()
        for f in fields:
            data = getattr(v, f.name)
            if isinstance(data, Sequence):
                for i in data:
                    results |= arg_visit(i)
            if isinstance(data, Mapping):
                for i in data.values():
                    results |= arg_visit(i)
            else:
                results |= arg_visit(data)
        return results


class CoroutineVisitor(GenericVisitor[Generator[A, B, None]]):
    def generic_visit(self, v: Any, *args: Any, **kwargs: Any) -> Generator[A, B, None]:
        def arg_visit(v: Any) -> Generator[A, B, None]:
            return self.visit(v, *args, **kwargs)

        try:
            fields = dataclasses.fields(v)
        except TypeError:
            return
        for f in fields:
            data = getattr(v, f.name)
            if isinstance(data, Sequence):
                for d in data:
                    yield from arg_visit(d)
            elif isinstance(data, Mapping):
                for d in data.values():
                    yield from arg_visit(d)
            else:
                yield from arg_visit(data)
        return


class UpdateVisitor(GenericVisitor[Any]):
    def __init__(self) -> None:
        self.visited_nodes: MMapping[int, Any] = {}

    def visit(self, v: A, *args: Any, **kwargs: Any) -> A:
        # Use already-visited object if it exists.
        # This makes handling trees with joins well-behaved.
        if self.id(v) in self.visited_nodes:
            return self.get_updated(v)
        visited: A = super().visit(v, *args, **kwargs)
        self.visited_nodes[self.id(v)] = visited
        return visited

    def get_updated(self, original: A) -> A:
        return cast(A, self.visited_nodes[self.id(original)])

    def id(self, obj: Any) -> Any:
        """
        Returns a unique identifier for a node. Can be overridden to
        modify the notion of equivalence.
        """
        return id(obj)

    def generic_visit(self, v: A, *args: Any, **kwargs: Any) -> A:
        try:
            fields = dataclasses.fields(v)
        except TypeError:
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
                res = [self.visit(x, *args, **kwargs) for x in data]
            elif isinstance(data, dict):
                res = {k: self.visit(v, *args, **kwargs) for k, v in data.items()}
            else:
                res = self.visit(data, *args, **kwargs)
            results[f.name] = res
        return v.__class__(**results)  # type: ignore
