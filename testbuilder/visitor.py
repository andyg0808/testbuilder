from typing import (
    Generic,
    Iterator,
    MutableMapping as MMapping,
    Sequence,
    TypeVar,
    Union,
    cast,
)

import dataclasses

# Generic types for visitors derived from
# http://logji.blogspot.com/2012/02/correcting-visitor-pattern.html


class Visitable:
    pass


A = TypeVar("A", bound=Visitable)
B = TypeVar("B")

Result = Union[Iterator[B], B]


class Visitor(Generic[A, B]):
    def visit(self, v: A) -> B:
        name = self.__class__.__name__
        func = getattr(self, "visit_" + name, self.generic_visit)
        return cast(B, func(v))

    def generic_visit(self, v: A) -> MMapping[str, Result]:
        results: MMapping[str, Result] = {}
        for f in dataclasses.fields(v):
            data = getattr(v, f.name)
            res: Result
            if isinstance(data, Sequence):
                res = map(self.visit, data)
            elif isinstance(data, Visitable):
                res = self.visit(cast(A, data))
            results[f.name] = res
        return results
