from typing import Any, Callable, Optional, Union


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


class LogRecord:
    channel: Optional[str] = None


class Handler:
    def __init__(
        self,
        level: Union[str, int] = 0,
        format_string: Optional[str] = None,
        filter: Optional[Callable[[LogRecord, "Handler"], bool]] = None,
        bubble: bool = False,
    ) -> None:
        ...

    def push_application(self) -> None:
        ...


class StderrHandler(Handler):
    pass
