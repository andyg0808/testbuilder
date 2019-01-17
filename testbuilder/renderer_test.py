from pathlib import Path

from . import ssa_basic_blocks as sbb
from .renderer import render_test
from .z3_types import bool_true


def test_expected_failure():
    test_data = sbb.TestData(
        name="Example",
        source_text="<code>",
        free_variables=[sbb.Variable("fish")],
        expression=bool_true,
        filepath=Path("/dev/null"),
    )
    actual = render_test(
        test=test_data, test_number=0, args={"fish": 44}, expected="fail::RuntimeError"
    )
    expected = """
import pytest
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
