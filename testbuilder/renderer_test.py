from pathlib import Path

from hypothesis import assume, given
from hypothesis.strategies import integers

from . import ssa_basic_blocks as sbb
from .hypothesis_entities import functions
from .renderer import render_test
from .z3_types import BOOL_TRUE


@given(functions, integers(), integers())
def test_generate_basic(op, a, b):
    assume(b != 0)
    function_name = op.__name__
    function_args = {"a": a, "b": b}
    function_expectation = op(a, b)
    function = render_test(
        sbb.ExpectedTestData(
            filepath=Path("mycode.py"),
            name=function_name,
            source_text="",
            free_variables=[sbb.Variable("a"), sbb.Variable("b")],
            expression=None,
            expected_result=function_expectation,
            args=function_args,
            test_number=0,
            target_line=1,
        )
    )
    expected = f"""
{op.__name__} = import_module("mycode").{op.__name__}
def test_{op.__name__}():
    a = {a}
    b = {b}
    actual = {op.__name__}(a, b)
    expected = {op(a, b)}
    assert renderer.convert_result(actual) == expected
    """
    assert function == expected


def test_expected_failure():
    test_data = sbb.ExpectedTestData(
        name="Example",
        source_text="<code>",
        free_variables=[sbb.Variable("fish")],
        expression=BOOL_TRUE,
        filepath=Path("/dev/null"),
        expected_result="fail::RuntimeError",
        args={"fish": 44},
        test_number=0,
        target_line=1,
    )
    actual = render_test(test_data)
    expected = """
Example = import_module("null").Example
def test_Example():
    fish = 44
    with pytest.raises(RuntimeError):
        Example(fish)
    """
    print("actual", actual)
    print("expected", expected)
    assert actual == expected
