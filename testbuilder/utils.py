import ast
import inspect
import re
import sys
from pprint import pprint
from typing import Any, NoReturn, Set, TypeVar, cast

import rainbow  # type: ignore
from .test_utils import write_dot

ObjString = re.compile(r"<\S+ object at \S+>")


def print_locations(node: ast.AST) -> None:
    for i in ast.walk(node):
        if not hasattr(i, "lineno") or not hasattr(i, "col_offset"):
            print("[31m" + str(i) + "[0m")
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


def dataclass_dump(code: Any) -> str:
    return colorize(code_format(ObjString.sub(r'"\0"', str(code))))


def ast_dump(
    code: Any, annotate_fields: bool = True, include_attributes: bool = True
) -> str:
    return colorize(
        code_format(
            ast.dump(
                code,
                annotate_fields=annotate_fields,
                include_attributes=include_attributes,
            )
        )
    )


def walker_print(obj: Any, prefix: str, seen: Set[int], hide: bool = False) -> None:
    """Dump `obj` in a brute-force way

    This is designed not to call any special operations as much as
    possible. It still uses normal `getattr`; in future, it might be
    good to eliminate that as well. The goal with this function is to
    get information about obj printing to the screen immediately, so
    that even very large objects can be inspected. The need for this
    came up during debugging, where formatting some values seemed to
    take an unknown long amount of time. This also looks for loops and
    prints out a clean message, so as to avoid being caught in an
    infinite loop.

    Arguments:
        obj: The object to print
        prefix: A string to prefix each printout line with. Empty
                string will do.
        seen: A set of `id` s which have been seen before. Empty set
              is fine as a user.
    """
    if id(obj) in seen:
        if not hide:
            print(prefix + "=", id(obj), "(seen)")
        return
    seen.add(id(obj))
    print(f"{prefix}={type(obj).__name__}@({id(obj)})", end="")
    field_count = 0
    field_numbers = []
    for field in dir(obj):
        if not field.startswith("_"):
            field_numbers.append(f"{field}_{field_count}")
            field_count += 1
    print("(", ", ".join(field_numbers), ")")
    for field in dir(obj):
        if not field.startswith("_"):
            walker_print(getattr(obj, field), prefix + "." + field, seen, hide)
    try:
        for k, v in obj.items():
            walker_print(v, prefix + "[" + str(k) + "]", seen, hide)
        return
    except AttributeError:
        # We don't have a dict here
        pass
    try:
        for i, o in enumerate(obj):
            walker_print(o, prefix + "[" + str(i) + "]", seen, hide)
        return
    except TypeError:
        # It's not enumerable, probably.
        pass


A = TypeVar("A")


class WriteDot:
    def __init__(self, filename: str) -> None:
        self.filename = filename

    def __call__(self, thing: A) -> A:
        write_dot(thing, self.filename)
        return thing
