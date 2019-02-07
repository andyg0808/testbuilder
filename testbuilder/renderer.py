import copy
import re
from importlib.machinery import SourceFileLoader
from typing import Any, Callable, Mapping, cast

from logbook import Logger

from .dataclass_utils import make_extended_instance
from .requester import Requester
from .ssa_basic_blocks import ExpectedTestData, SolvedTestData

ThrowParser = re.compile(r"fail::(\w+)$")

log = Logger("renderer")


def prompt_for_test(
    requester: Requester, prompt: str, test: SolvedTestData
) -> ExpectedTestData:
    requester.output("=================================================")
    requester.formatted_output(test.source_text)
    expected = ""
    if prompt == "":
        requester.output("Suppose we pass the following arguments:")
        requester.formatted_output(str(test.args))
        expected = requester.input(
            f"What is the expected output of {test.name} from these arguments? "
        )
    else:
        expected = requester.input(prompt)
    return make_extended_instance(test, ExpectedTestData, expected_result=expected)


def get_test_func(test: SolvedTestData) -> Callable[..., Any]:
    try:
        loader = SourceFileLoader("mod" + test.filepath.stem, str(test.filepath))
        mod = loader.load_module()  # type: ignore
        return cast(Callable[..., Any], getattr(mod, test.name))
    except FileNotFoundError:
        glo = globals()
        loc: Mapping[str, Any] = {}
        exec(test.source_text, glo, loc)
        funcs = list(loc.values())
        return cast(Callable[..., Any], funcs[0])


def run_for_test(
    requester: Requester, func: Callable[..., Any], test: SolvedTestData
) -> ExpectedTestData:
    requester.output(f"Generating test {test.test_number} for {test.name}")
    args = copy.deepcopy(test.args)
    try:
        result = func(**args)
    except Exception as e:
        result = f"fail::{type(e)}"
    return make_extended_instance(test, ExpectedTestData, expected_result=str(result))


def render_test(test: ExpectedTestData) -> str:
    keys = [x.id for x in test.free_variables]
    arg_strings = [f"{key} = {repr(test.args[key])}" for key in keys]
    args_string = "\n    ".join(arg_strings)
    call_args_string = ", ".join(keys)
    call_string = f"{test.name}({call_args_string})"
    expected = str(test.expected_result).strip()
    log.info(f"Building test number {test.test_number}")
    boilerplate = """from importlib import import_module
from testbuilder.pair import Pair"""
    if test.test_number > 0:
        number_str = f"_{test.test_number+1}"
    else:
        number_str = ""
    throw_match = ThrowParser.match(expected)
    if throw_match:
        exception_name = throw_match[1]
        return f"""
import pytest
{boilerplate}
{test.name} = import_module("{test.filepath.stem}").{test.name}
def test_{test.name}{number_str}():
    {args_string}
    with pytest.raises({exception_name}):
        {call_string}
    """
    else:
        # See https://stackoverflow.com/a/38813946/2243495
        # This allows correct importing of modules with unacceptable
        # Python names
        return f"""
{boilerplate}
{test.name} = import_module("{test.filepath.stem}").{test.name}
def test_{test.name}{number_str}():
    {args_string}
    actual = {call_string}
    expected = {expected}
    assert actual == expected
    """
