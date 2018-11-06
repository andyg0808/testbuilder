from io import StringIO
from pathlib import Path

from hypothesis import assume, given
from hypothesis.strategies import integers

from .generate import generate_tests
from .hypothesis_entities import functions
from .renderer import render_test

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
        source=Path("mycode.py"),
        name=function_name,
        test_number=0,
        args=function_args,
        expected=function_expectation,
    )
    expected = f"""
from mycode import {op.__name__}
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
        source=Path("mycode.py"),
        name=function_name,
        test_number=0,
        args=function_args,
        expected=function_expectation,
    )
    expected = """
from mycode import min
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
    io = StringIO("")
    tests = generate_tests(Path("boring.py"), code, io)
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
from boring import boring
def test_boring():
    fishy = 1234567890
    actual = boring(fishy)
    expected = 36
    assert actual == expected
    """,
        """
from boring import caller
def test_caller():
    fishy = None
    actual = caller(fishy)
    expected = 36
    assert actual == expected
    """,
    }
    io = StringIO("36\n36\n")
    tests = generate_tests(Path("boring.py"), code, io)
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
