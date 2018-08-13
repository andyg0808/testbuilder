from typing import Callable, TypeVar


def compose(*funcs: Callable) -> Callable:
    ...


T = TypeVar("T")
U = TypeVar("U")


def pipe(data: T, *funcs: Callable) -> U:
    ...
