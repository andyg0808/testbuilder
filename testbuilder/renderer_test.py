from pathlib import Path

from . import ssa_basic_blocks as sbb
from .renderer import render_test
from .z3_types import BOOL_TRUE


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
    )
    actual = render_test(test_data)
    expected = """
import pytest
from importlib import import_module
from testbuilder.pair import Pair
Example = import_module("null").Example
def test_Example():
    fish = 44
    with pytest.raises(RuntimeError):
        Example(fish)
    """
    print("actual", actual)
    print("expected", expected)
    assert actual == expected
