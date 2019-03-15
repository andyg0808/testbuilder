import copy
import inspect
import re
import sys
from importlib import import_module
from pathlib import Path
from typing import Any, Callable, Mapping, cast

from logbook import Logger

from ._extern_utils import convert_result
from .dataclass_utils import make_extended_instance
from .requester import Requester
from .ssa_basic_blocks import ExpectedTestData, SolvedTestData
from .z3_types import GenerationError

ThrowParser = re.compile(r"fail::(\w+)$")

log = Logger("renderer")


class MissingGolden(AttributeError):
    pass


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


def get_golden_func(name: str, golden: Path) -> Callable[..., Any]:
    sys.path.append(golden.parent.as_posix())
    mod = import_module(golden.stem)
    sys.path.pop()
    golden = getattr(mod, name, None)
    if golden is None:
        raise MissingGolden()
    return cast(Callable[..., Any], golden)


def get_test_func(test: SolvedTestData) -> Callable[..., Any]:
    loc: Mapping[str, Any] = {}
    exec(test.source_text, {}, loc)
    funcs = list(loc.values())
    return cast(Callable[..., Any], funcs[0])


def run_for_test(
    requester: Requester, func: Callable[..., Any], test: SolvedTestData, skipfail: bool
) -> ExpectedTestData:
    requester.output(
        f"Generating test {test.test_number} for {test.name} at line {test.target_line}"
    )
    # args = copy.deepcopy(test.args)
    sig = inspect.signature(func)
    args = {}
    for param in sig.parameters:
        args[param] = test.args[param]
    try:
        result = func(**args)
        writeout = repr(convert_result(result))
    except Exception as e:
        if skipfail:
            log.warn(f"Skipping test due to code run failure: {e}[0m")
            raise GenerationError() from e
        log.warn(f"Asserting failure due to code run failure: {e}")
        result = f"fail::{type(e).__name__}"
        writeout = result
    log.debug(
        f"""Expected result information:
        Type: {type(result)}
        Attrs: `{'`, `'.join(dir(result))}`
        repr:
{repr(result)}
        repr(converted):
{repr(writeout)}"""
    )
    return make_extended_instance(test, ExpectedTestData, expected_result=writeout)


def render_test(test: ExpectedTestData) -> str:
    keys = [x.id for x in test.free_variables]
    arg_strings = [f"{key} = {repr(test.args[key])}" for key in keys]
    args_string = "\n    ".join(arg_strings)
    call_args_string = ", ".join(keys)
    call_string = f"{test.name}({call_args_string})"
    expected = str(test.expected_result).strip()
    log.info(f"Building test number {test.test_number}")
    if test.test_number > 0:
        number_str = f"_{test.test_number+1}"
    else:
        number_str = ""
    throw_match = ThrowParser.match(expected)
    if throw_match:
        exception_name = throw_match[1]
        return f"""
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
{test.name} = import_module("{test.filepath.stem}").{test.name}
def test_{test.name}{number_str}():
    {args_string}
    actual = {call_string}
    expected = {expected}
    assert convert_result(actual) == expected
    """
