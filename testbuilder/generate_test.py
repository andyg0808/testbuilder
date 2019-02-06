import sys
from pathlib import Path
from tempfile import NamedTemporaryFile, TemporaryDirectory
from unittest.mock import create_autospec

from hypothesis import assume, given
from hypothesis.strategies import integers

from . import requester, ssa_basic_blocks as sbb
from .generate import generate_tests
from .hypothesis_entities import functions
from .renderer import render_test


def Requester():
    return create_autospec(requester.Requester)()


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
        )
    )
    expected = f"""
from importlib import import_module
from testbuilder.pair import Pair
{op.__name__} = import_module("mycode").{op.__name__}
def test_{op.__name__}():
    a = {a}
    b = {b}
    actual = {op.__name__}(a, b)
    expected = {op(a, b)}
    assert actual == expected
    """
    assert function == expected


def test_generate_list_handler():
    function_name = "min"
    function_args = {"a": [1, 2, 3]}
    function_expectation = 1
    function = render_test(
        sbb.ExpectedTestData(
            filepath=Path("mycode.py"),
            name=function_name,
            source_text="",
            free_variables=[sbb.Variable("a")],
            expression=None,
            expected_result=function_expectation,
            args=function_args,
            test_number=0,
        )
    )
    expected = """
from importlib import import_module
from testbuilder.pair import Pair
min = import_module("mycode").min
def test_min():
    a = [1, 2, 3]
    actual = min(a)
    expected = 1
    assert actual == expected
    """
    assert function == expected


def test_generate_uninteresting_function():
    code = """
def boring(fishy):
    24
    fishy
    # This line should throw a NameError, so we want to at least run
    # the code in our test.
    garbage
    """
    expected = [
        # Eventually, we want to generate a test that just runs the
        # code with appropriate inputs if we can't find any lines to
        # test. But for now, we'll just not generate any tests.
        #         """
        # from minmax import maximize
        # def test_maximize():
        #     fishy = 0
        #     boring(fishy)
        #     """
    ]
    requester = Requester()
    requester.input.return_value = ""
    tests = generate_tests(Path("boring.py"), code, requester)
    assert requester.input.call_count == 0
    assert tests == expected


def test_uninteresting_function_call():
    code = """
def boring(fishy):
    fishy
    return 36

def caller(fishy):
    return boring(fishy)
    """
    expected = {
        """
from importlib import import_module
from testbuilder.pair import Pair
boring = import_module("boring").boring
def test_boring():
    fishy = 1234567890
    actual = boring(fishy)
    expected = 36
    assert actual == expected
    """,
        """
from importlib import import_module
from testbuilder.pair import Pair
caller = import_module("boring").caller
def test_caller():
    fishy = None
    actual = caller(fishy)
    expected = 36
    assert actual == expected
    """,
    }
    requester = Requester()
    requester.input.side_effect = ["36", "36"]
    tests = generate_tests(Path("boring.py"), code, requester)
    assert requester.input.call_count == 2
    assert set(tests) == expected


def test_autosolve():
    code = """
def id(x):
    return x
    """
    expected = {
        """
from importlib import import_module
from testbuilder.pair import Pair
id = import_module("id").id
def test_id():
    x = 0
    actual = id(x)
    expected = 0
    assert actual == expected
    """
    }

    requester = Requester()
    tests = generate_tests(
        source=Path("id.py"), text=code, requester=requester, autosolve=True
    )
    requester.input.assert_not_called()
    assert set(tests) == expected


def test_autosolve_real_module():
    code = """
from math import sin
def example(val):
    return sin(val)
    """
    requester = Requester()
    with TemporaryDirectory() as d:
        with NamedTemporaryFile(suffix=".py", mode="w", dir=d) as fi:
            fi.write(code)
            fi.flush()
            tests = generate_tests(
                source=Path(fi.name), text=code, requester=requester, autosolve=True
            )
            sys.path.append(d)
            for test in tests:
                exec(test)
            sys.path.pop()
    requester.input.assert_not_called()
