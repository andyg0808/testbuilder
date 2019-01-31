from typing import Callable, Iterable, List, Mapping, Sequence, TypeVar, overload


def compose(*funcs: Callable) -> Callable:
    ...


T = TypeVar("T")
U = TypeVar("U")

# As seen in https://github.com/python/typeshed/blob/ad803e1caa9764e8778ce558fb99e7d4cca3cda9/stdlib/2and3/builtins.pyi
_T1 = TypeVar("_T1")
_T2 = TypeVar("_T2")
_T3 = TypeVar("_T3")
_T4 = TypeVar("_T4")
_T5 = TypeVar("_T5")
_T6 = TypeVar("_T6")
_T7 = TypeVar("_T7")


def pipe(data: T, funcs: Callable[[T], _T1]) -> _T1:
    ...


@overload
def pipe(data: T, func1: Callable[[T], _T1], func2: Callable[[_T1], _T2]) -> _T2:
    ...


@overload
def pipe(
    data: T,
    func1: Callable[[T], _T1],
    func2: Callable[[_T1], _T2],
    func3: Callable[[_T2], _T3],
) -> _T3:
    ...


@overload
def pipe(
    data: T,
    func1: Callable[[T], _T1],
    func2: Callable[[_T1], _T2],
    func3: Callable[[_T2], _T3],
    func4: Callable[[_T3], _T4],
) -> _T4:
    ...


@overload
def pipe(data: T, funcs: Callable) -> U:
    ...


def mapcat(func: Callable[[T], Iterable[U]], seqs: Iterable[T]) -> Sequence[U]:
    ...


def concat(seqs: Iterable[Iterable[T]]) -> Iterable[T]:
    ...


def groupby(key: Callable[[T], U], seq: Iterable[T]) -> Mapping[U, List[T]]:
    ...
