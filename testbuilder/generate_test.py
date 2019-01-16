from pathlib import Path
from unittest.mock import Mock, call, create_autospec

from hypothesis import assume, given
from hypothesis.strategies import integers

from testbuilder.pair import Pair

from . import requester, ssa_basic_blocks as sbb
from .generate import generate_tests
from .hypothesis_entities import functions
from .renderer import render_test

Requester = create_autospec(requester.Requester)
# def test_generation():
#     code = """
# def maximize(a, b):
#     if a < b:
#         return b
#     else:
#         return a

# def minimize(a, b):
#     if a < b:
#         return a
#     else:
#         return b
#     """
#     expected = [
#         """
# from minmax import maximize
# def test_maximize():
#     a = 0
#     b = 1
#     actual = maximize(a, b)
#     expected = 1
#     assert actual == expected
#     """,
#         """
# from minmax import maximize
# def test_maximize_2():
#     a = 0
#     b = -38
#     actual = maximize(a, b)
#     expected = 0
#     assert actual == expected
#     """,
#         """
# from minmax import minimize
# def test_minimize_3():
#     a =
#         """,
#         """
# from minmax import minimize
# def test_minimize():
#     a = 0
#     b = 1
#     actual = minimize(a, b)
#     expected = 0
#     assert actual == expected
#     """,
#         """
# from minmax import minimize
# def test_minimize_2():
#     a = 0
#     b = 0
#     actual = minimize(a, b)
#     expected = 0
#     assert actual == expected
#     """,
#     ]
#     io = StringIO("1\n0\n0\n0\n")
#     tests = generate_tests(Path("minmax.py"), code, io)
#     assert tests == expected


@given(functions, integers(), integers())
def test_generate_basic(op, a, b):
    assume(b != 0)
    function_name = op.__name__
    function_args = {"a": a, "b": b}
    function_expectation = op(a, b)
    function = render_test(
        test_number=0,
        test=sbb.TestData(
            filepath=Path("mycode.py"),
            name=function_name,
            source_text="",
            free_variables=[sbb.Variable("a"), sbb.Variable("b")],
            expression=None,
        ),
        args=function_args,
        expected=function_expectation,
    )
    expected = f"""
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
        test_number=0,
        test=sbb.TestData(
            filepath=Path("mycode.py"),
            name=function_name,
            source_text="",
            free_variables=[sbb.Variable("a")],
            expression=None,
        ),
        args=function_args,
        expected=function_expectation,
    )
    expected = """
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
from testbuilder.pair import Pair
boring = import_module("boring").boring
def test_boring():
    fishy = 1234567890
    actual = boring(fishy)
    expected = 36
    assert actual == expected
    """,
        """
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


# @given(function_names, integers(), integers())
# def test_run_test(testname, n, k):
#    assume(n != k)
#    failed_code = f"""
# def {testname}():
#    assert {n} == {k}
# """
#
#    code = f"""
# def {testname}():
#    assert {n} == {n}
# """
#
#    with pytest.raises(AssertionError):
#        run_test(testname, failed_code)
#    run_test(testname, code)
