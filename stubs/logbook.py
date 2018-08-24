from typing import Any


def critical(*args: Any, **kwargs: Any) -> None:
    ...


def error(*args: Any, **kwargs: Any) -> None:
    ...


def warn(*args: Any, **kwargs: Any) -> None:
    ...


def warning(*args: Any, **kwargs: Any) -> None:
    ...


def notice(*args: Any, **kwargs: Any) -> None:
    ...


def debug(*args: Any, **kwargs: Any) -> None:
    ...


def info(*args: Any, **kwargs: Any) -> None:
    ...


class Logger:
    def __init__(self, name: str) -> None:
        ...

    def critical(self, *args: Any, **kwargs: Any) -> None:
        ...

    def error(self, *args: Any, **kwargs: Any) -> None:
        ...

    def warn(self, *args: Any, **kwargs: Any) -> None:
        ...

    def warning(self, *args: Any, **kwargs: Any) -> None:
        ...

    def notice(self, *args: Any, **kwargs: Any) -> None:
        ...

    def debug(self, *args: Any, **kwargs: Any) -> None:
        ...

    def info(self, *args: Any, **kwargs: Any) -> None:
        ...
