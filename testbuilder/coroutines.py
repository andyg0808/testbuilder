import inspect
from typing import Generator, Generic, List, TypeVar, cast

T = TypeVar("T")
U = TypeVar("U")


def result(xs: Generator[None, T, U], val: T) -> U:
    run_to_suspend(xs)
    return retrieve(xs, val)


def gather(xs: Generator[T, None, None]) -> List[T]:
    return list(xs)


def run_to_suspend(xs: Generator[None, T, U]) -> Generator[None, T, U]:
    if not inspect.isgenerator(xs):
        raise RuntimeError(f"{xs} is not a generator. Perhaps a yield is missing?")
    # Start generator
    try:
        # Run to yield
        next(xs)
    except TypeError as ex:
        raise RuntimeError(f"No yields in {xs}! Exactly one yield is required.") from ex
    return xs


def retrieve(xs: Generator[None, T, U], val: T) -> U:
    if not inspect.isgenerator(xs):
        raise RuntimeError(f"{xs} is not a generator. Perhaps a yield is missing?")
    try:
        # Finish generator
        xs.send(val)
    except StopIteration as stop:
        return cast(U, stop.value)
    raise RuntimeError(f"Too many yields in {xs}!")
