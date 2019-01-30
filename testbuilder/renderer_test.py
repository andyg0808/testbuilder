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
    )
    actual = render_test(test=test_data, test_number=0, args={"fish": 44})
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
