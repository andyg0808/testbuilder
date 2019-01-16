from typing import Any, Mapping

from logbook import Logger

from .requester import Requester
from .ssa_basic_blocks import TestData

log = Logger("renderer")


def prompt_and_render_test(
    requester: Requester,
    prompt: str,
    test: TestData,
    test_number: int,
    args: Mapping[str, Any],
) -> str:
    requester.output("=================================================")
    requester.formatted_output(test.source_text)
    expected = ""
    if prompt == "":
        requester.output("Suppose we pass the following arguments:")
        requester.formatted_output(str(args))
        expected = requester.input(
            f"What is the expected output of {test.name} from these arguments? "
        )
    else:
        expected = requester.input(prompt)
    return render_test(test=test, test_number=test_number, args=args, expected=expected)


def render_test(
    test: TestData, test_number: int, args: Mapping[str, Any], expected: Any
) -> str:
    keys = [x.id for x in test.free_variables]
    arg_strings = [f"{key} = {repr(args[key])}" for key in keys]
    args_string = "\n    ".join(arg_strings)
    call_args_string = ", ".join(keys)
    call_string = f"{test.name}({call_args_string})"
    expected = str(expected).strip()
    log.info(f"Building test number {test_number}")
    if test_number > 0:
        number_str = f"_{test_number+1}"
    else:
        number_str = ""
    # See https://stackoverflow.com/a/38813946/2243495
    # This allows correct importing of modules with unacceptable
    # Python names
    return f"""
from testbuilder.pair import Pair
{test.name} = import_module("{test.filepath.stem}").{test.name}
def test_{test.name}{number_str}():
    {args_string}
    actual = {call_string}
    expected = {expected}
    assert actual == expected
    """
