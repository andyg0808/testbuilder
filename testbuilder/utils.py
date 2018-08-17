import ast
import inspect
from pprint import pprint
from typing import Any

from termcolor import cprint


def print_locations(node):
    for i in ast.walk(node):
        if not hasattr(i, "lineno") or not hasattr(i, "col_offset"):
            cprint(i, "red")
        else:
            print(
                "{} line={} col={}".format(
                    i, getattr(i, "lineno", "none"), getattr(i, "col_offset", "none")
                )
            )


def crash(reason: str = ""):
    if reason:
        raise RuntimeError("Crashing because" + reason)
    raise RuntimeError("Crashing!")


def pipe_print(value: Any, message: str = "") -> Any:
    if message == "":
        stack = inspect.stack()
        assert len(stack) > 0
        caller = stack[0]
        print(f"Pipe printing for {caller.function}")
        del caller
    else:
        print(message)
    pprint(value)
    print("End pipe print")
    return value
