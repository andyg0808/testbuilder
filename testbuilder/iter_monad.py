from functools import partial, reduce
from typing import (
    Any,
    Callable,
    Generic,
    Iterator,
    List,
    Mapping,
    Optional,
    TypeVar,
    cast,
)

from toolz import compose, pipe

A = TypeVar("A")
B = TypeVar("B")
T = TypeVar("T")


def liftIter(func: Callable[[A], B]) -> Callable[[Iterator[A]], Iterator[B]]:
    def _lift(i: Iterator[A]) -> Iterator[B]:
        return map(func, i)

    return _lift


def bind(data: Iterator[A], func: Callable[[A], Iterator[B]]) -> Iterator[B]:
    for v in data:
        for x in func(v):
            yield x


def chain(*func: Callable[[A], Iterator[B]]) -> Callable[[Iterator[A]], Iterator[B]]:
    def _chain(data: Iterator[A]) -> Iterator[B]:
        # reversed necessary to call functions in normal composition order
        return reduce(bind, reversed(func), data)  # type: ignore

    return _chain


def returnIter(v: A) -> Iterator[A]:
    yield v


def optional_to_iter(v: Optional[A]) -> Iterator[A]:
    if v is None:
        return iter([])
    else:
        return returnIter(v)
