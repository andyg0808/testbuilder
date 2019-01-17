import ast
import inspect
import sys
from pprint import pprint
from typing import Any, NoReturn, TypeVar, cast

from termcolor import cprint

import rainbow  # type: ignore

from .test_utils import write_dot


def print_locations(node: ast.AST) -> None:
    for i in ast.walk(node):
        if not hasattr(i, "lineno") or not hasattr(i, "col_offset"):
            cprint(str(i), "red")
        else:
            print(
                "{} line={} col={}".format(
                    i, getattr(i, "lineno", "none"), getattr(i, "col_offset", "none")
                )
            )


def crash(reason: str = "") -> NoReturn:
    if reason:
        print("Crashing because" + reason, file=sys.stderr)
    print("Crashing!", file=sys.stderr)
    caller = inspect.stack()[1]
    print(
        f"at {caller.filename} line {caller.lineno}, in {caller.function}",
        file=sys.stderr,
    )
    sys.exit(42)


def pipe_print(value: Any, message: str = "") -> Any:
    if message == "":
        stack = inspect.stack()
        assert len(stack) > 2
        caller = stack[2]
        print(f"Pipe printing for {caller.function}")
        del caller
    else:
        print(message)
    pprint(value)
    print("End pipe print")
    return value


def code_format(value: Any, message: str = "") -> str:
    import black  # type: ignore
    from .requester import format
    import shutil

    width = shutil.get_terminal_size().columns
    return black.format_str(str(value), width)  # type: ignore


Replacer = rainbow.Replacer(colorize=True)


def colorize(code: str) -> str:
    return cast(str, Replacer.color(code))


A = TypeVar("A")


class WriteDot:
    def __init__(self, filename: str) -> None:
        self.filename = filename

    def __call__(self, thing: A) -> A:
        write_dot(thing, self.filename)
        return thing
