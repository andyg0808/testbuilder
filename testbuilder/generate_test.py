from io import StringIO
from pathlib import Path

import pytest
from hypothesis import assume, given
from hypothesis.strategies import integers

from .generate import run_test
from .generate_proto import generate_tests
from .hypothesis_entities import function_names, functions
from .renderer import render_test


def test_generation():
    code = """
def maximize(a, b):
    if a < b:
        return b
    else:
        return a

def minimize(a, b):
    if a < b:
        return a
    else:
        return b
    """
    expected = [
        """
from minmax import maximize
def test_maximize():
    a = 0
    b = 1
    actual = maximize(a, b)
    expected = 1
    assert actual == expected
    """,
        """
from minmax import maximize
def test_maximize():
    a = 0
    b = 0
    actual = maximize(a, b)
    expected = 0
    assert actual == expected
    """,
        """
from minmax import minimize
def test_minimize():
    a = 0
    b = 1
    actual = minimize(a, b)
    expected = 0
    assert actual == expected
    """,
        """
from minmax import minimize
def test_minimize():
    a = 0
    b = 0
    actual = minimize(a, b)
    expected = 0
    assert actual == expected
    """,
    ]
    io = StringIO("1\n0\n0\n0\n")
    tests = generate_tests(Path("minmax.py"), code, io)
    assert tests == expected


@given(functions, integers(), integers())
def test_generate_basic(op, a, b):
    assume(b != 0)
    function_name = op.__name__
    function_args = {"a": a, "b": b}
    function_expectation = op(a, b)
    function = render_test(
        Path("mycode.py"), function_name, function_args, function_expectation
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
        Path("mycode.py"), function_name, function_args, function_expectation
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
