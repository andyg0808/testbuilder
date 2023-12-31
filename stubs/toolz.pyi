from typing import Any, Callable, Iterable, List, Mapping, Sequence, TypeVar, overload

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


def compose(*funcs: Callable[..., Any]) -> Callable[..., Any]:
    ...


@overload
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
def pipe(
    data: T,
    func1: Callable[[T], _T1],
    func2: Callable[[_T1], _T2],
    func3: Callable[[_T2], _T3],
    func4: Callable[[_T3], _T4],
    func5: Callable[[_T4], _T5],
) -> _T5:
    ...
@overload
def pipe(
    data: T,
    func1: Callable[[T], _T1],
    func2: Callable[[_T1], _T2],
    func3: Callable[[_T2], _T3],
    func4: Callable[[_T3], _T4],
    func5: Callable[[_T4], _T5],
    func6: Callable[[_T5], _T6],
) -> _T6:
    ...
@overload
def pipe(
    data: T,
    func1: Callable[[T], _T1],
    func2: Callable[[_T1], _T2],
    func3: Callable[[_T2], _T3],
    func4: Callable[[_T3], _T4],
    func5: Callable[[_T4], _T5],
    func6: Callable[[_T5], _T6],
    func7: Callable[[_T6], _T7],
) -> _T7:
    ...


# mypy doesn't accept this currently, although I think it's more
# general than the other overloads
# @overload
# def pipe(data: T, funcs: Callable[..., Any]) -> U:
#     ...


def mapcat(func: Callable[[T], Iterable[U]], seqs: Iterable[T]) -> Sequence[U]:
    ...


def concat(seqs: Iterable[Iterable[T]]) -> Iterable[T]:
    ...


def groupby(key: Callable[[T], U], seq: Iterable[T]) -> Mapping[U, List[T]]:
    ...
