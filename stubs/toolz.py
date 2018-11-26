from typing import Callable, Iterable, List, Mapping, Sequence, TypeVar


def compose(*funcs: Callable) -> Callable:
    ...


T = TypeVar("T")
U = TypeVar("U")


def pipe(data: T, *funcs: Callable) -> U:
    ...


def mapcat(func: Callable[[T], Iterable[U]], seqs: Iterable[T]) -> Sequence[U]:
    ...


def concat(seqs: Iterable[Iterable[T]]) -> Iterable[T]:
    ...


def groupby(key: Callable[[T], U], seq: Iterable[T]) -> Mapping[U, List[T]]:
    ...
