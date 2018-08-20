import inspect
from typing import (
    Any,
    Callable,
    Generic,
    Iterator,
    MutableMapping as MMapping,
    Sequence,
    Type,
    TypeVar,
    Union,
    cast,
)

import dataclasses

# Generic types for visitors derived from
# http://logji.blogspot.com/2012/02/correcting-visitor-pattern.html


class Visitable:
    pass


A = TypeVar("A")
B = TypeVar("B")

Result = Union[Iterator[B], B]


class VisitError(NotImplementedError):
    pass


class SimpleVisitor(Generic[B]):
    T = TypeVar("T")

    def visit(self, v: Any, *args: Any) -> B:
        func = self.__find_function(v.__class__)
        return func(v, *args)

    def __find_function(self, start_class: Type) -> Callable[..., B]:
        cache = getattr(self, "__fun_cache", {})
        if start_class in cache:
            return cache[start_class]
        for cls in inspect.getmro(start_class):
            func = self.__scan_functions(cls)
            if func is not None:
                cache[start_class] = func
                setattr(self, "__fun_cache", cache)
                return cast(Callable[..., B], func)
        raise VisitError(f"No handler for {start_class}")

    def __scan_functions(self, target_class: Type) -> Callable[..., B]:
        typecache = getattr(self, "__type_cache", None)
        if typecache is None:
            typecache = {}
            # See https://stackoverflow.com/a/1911287/
            for name, method in inspect.getmembers(self, inspect.ismethod):
                if not name.startswith("visit_"):
                    continue
                signature = inspect.signature(method)
                if len(signature.parameters) < 1:
                    continue
                parameters = list(signature.parameters.values())
                param = parameters[0]
                typecache[param.annotation] = method
            setattr(self, "__type_cache", typecache)
        return typecache.get(target_class, None)


V = TypeVar("V", bound=Visitable)


class Visitor(SimpleVisitor[B], Generic[V, B]):
    def generic_visit(self, v: A) -> MMapping[str, Result]:
        results: MMapping[str, Result] = {}
        for f in dataclasses.fields(v):
            data = getattr(v, f.name)
            res: Result
            if isinstance(data, Sequence):
                res = map(self.visit, data)
            elif isinstance(data, Visitable):
                res = self.visit(cast(V, data))
            results[f.name] = res
        return results
