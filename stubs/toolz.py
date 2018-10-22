from typing import Callable, Iterable, Sequence, TypeVar


def compose(*funcs: Callable) -> Callable:
    ...


T = TypeVar("T")
U = TypeVar("U")


def pipe(data: T, *funcs: Callable) -> U:
    ...


def mapcat(func: Callable[[T], Sequence[U]], seqs: Sequence[T]) -> Sequence[U]:
    ...


def concat(seqs: Iterable[Iterable[T]]) -> Iterable[T]:
    ...
