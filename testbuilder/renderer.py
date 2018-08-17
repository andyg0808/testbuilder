from ast import FunctionDef
from pathlib import Path
from typing import Any, Mapping

from astor import to_source  # type: ignore


def prompt_and_render_test(
    source: Path,
    name: str,
    io: Any,
    prompt: str,
    text: str,
    func: FunctionDef,
    args: Mapping[str, Any],
) -> str:
    print("=================================================")
    # print(text)
    print(to_source(func))
    if prompt == "":
        print(f"What is the expected output of {name} from these arguments? {args}")
    else:
        print(prompt)
    expected = io.readline()
    return render_test(source, name, args, expected)


def render_test(source: Path, name: str, args: Mapping[str, Any], expected: Any) -> str:
    keys = [x for x in sorted(args.keys()) if x != "ret"]
    arg_strings = [f"{key} = {args[key]}" for key in keys]
    args_string = "\n    ".join(arg_strings)
    call_args_string = ", ".join(keys)
    call_string = f"{name}({call_args_string})"
    expected = str(expected).strip()
    # print("callstring", call_string)
    return f"""
from {source.stem} import {name}
def test_{name}():
    {args_string}
    actual = {call_string}
    expected = {expected}
    assert actual == expected
    """
