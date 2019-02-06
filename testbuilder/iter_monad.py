from functools import reduce
from typing import Callable, Iterable, Iterator, Optional, TypeVar, Union

A = TypeVar("A")
B = TypeVar("B")
T = TypeVar("T")


def liftIter(func: Callable[[A], B]) -> Callable[[Iterable[A]], Iterator[B]]:
    """
    Takes a function which operates on individual values and returns a
    function which operates on iterators of such values. Lifts a
    function into the iterator monad
    """

    def _lift(i: Iterable[A]) -> Iterator[B]:
        return map(func, i)

    return _lift


def bind(data: Iterable[A], func: Callable[[A], Iterable[B]]) -> Iterator[B]:
    """
    Takes a function converting values to iterators and an iterator
    and concatenates the iterators resulting from running the function
    on each value end to end.
    """
    for v in data:
        for x in func(v):
            yield x


def chain(*func: Callable[[A], Iterable[B]]) -> Callable[[Iterable[A]], Iterator[B]]:
    """
    Takes a function taking values to iterators and returns a function
    taking an iterator and returning the concatenation of all the
    resulting iterators.
    """

    def _chain(data: Iterable[A]) -> Iterator[B]:
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
