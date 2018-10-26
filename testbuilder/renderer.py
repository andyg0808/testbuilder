from pathlib import Path
from typing import Any, Mapping

from .ssa_basic_blocks import TestData


def prompt_and_render_test(
    source: Path,
    name: str,
    io: Any,
    prompt: str,
    text: str,
    test: TestData,
    test_number: int,
    args: Mapping[str, Any],
) -> str:
    print("=================================================")
    # print(text)
    print(test.source_text)
    if prompt == "":
        print(f"What is the expected output of {name} from these arguments? {args}")
    else:
        print(prompt)
    expected = io.readline()
    return render_test(source, name, test_number, args, expected)


def render_test(
    source: Path, name: str, test_number: int, args: Mapping[str, Any], expected: Any
) -> str:
    keys = [x for x in sorted(args.keys()) if x != "ret"]
    arg_strings = [f"{key} = {args[key]}" for key in keys]
    args_string = "\n    ".join(arg_strings)
    call_args_string = ", ".join(keys)
    call_string = f"{name}({call_args_string})"
    expected = str(expected).strip()
    print("Test number", test_number)
    if test_number > 0:
        number_str = f"_{test_number+1}"
    else:
        number_str = ""
    # print("callstring", call_string)
    return f"""
from {source.stem} import {name}
def test_{name}{number_str}():
    {args_string}
    actual = {call_string}
    expected = {expected}
    assert actual == expected
    """
