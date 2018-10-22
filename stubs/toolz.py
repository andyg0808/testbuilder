from typing import Callable, Iterable, List, Mapping, Sequence, TypeVar


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


def groupby(key: Callable[[T], U], seq: Sequence[T]) -> Mapping[U, List[T]]:
    ...
