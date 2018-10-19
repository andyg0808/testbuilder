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
    """
    Takes a function which operates on individual values and returns a
    function which operates on iterators of such values. Lifts a
    function into the iterator monad
    """

    def _lift(i: Iterator[A]) -> Iterator[B]:
        return map(func, i)

    return _lift


def bind(data: Iterator[A], func: Callable[[A], Iterator[B]]) -> Iterator[B]:
    """
    Takes a function converting values to iterators and an iterator
    and concatenates the iterators resulting from running the function
    on each value end to end.
    """
    for v in data:
        for x in func(v):
            yield x


def chain(*func: Callable[[A], Iterator[B]]) -> Callable[[Iterator[A]], Iterator[B]]:
    """
    Takes a function taking values to iterators and returns a function
    taking an iterator and returning the concatenation of all the
    resulting iterators.
    """

    def _chain(data: Iterator[A]) -> Iterator[B]:
        # reversed necessary to call functions in normal composition order
        return reduce(bind, reversed(func), data)  # type: ignore

    return _chain


def returnIter(v: A) -> Iterator[A]:
    """
    Lifts a value into iterator context
    """
    yield v


def optional_to_iter(v: Optional[A]) -> Iterator[A]:
    """
    Converts an Optional value into an iterator. If a value is
    present, the iterator contains a value. If not, it is of zero
    length.
    """
    if v is None:
        return iter([])
    else:
        return returnIter(v)
