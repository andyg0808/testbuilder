import ast

import pytest

import z3

from .expression_builder import get_expression
from .solver import solve
from .variable_expander import expand_variables


def compare_dicts(actual, expected):
    if expected is None:
        assert actual is None
        return
    else:
        assert actual is not None
    keys = actual.keys() | expected.keys()
    for k in keys:
        left = actual[k]
        right = expected[k]
        assert type(left) == type(right)
        assert left == right


def check_solve(code, conditions, expected, unroll=1):
    parse = ast.parse(code)
    code_expression = get_expression(-1, parse, depth=unroll)
    if conditions:
        condition_expression = expand_variables(conditions)
        expression = z3.And(code_expression, condition_expression)
    else:
        expression = code_expression
    print("expression", expression)
    res = solve(expression)
    if isinstance(expected, spotcheck):
        expected.check(res)
    else:
        compare_dicts(res, expected)


def test_basic_solution():
    check_solve(
        """
def test(a):
    return a
    """,
        "ret == 4",
        {"a": 4, "ret": 4},
    )


def test_arithmetic_solution():
    check_solve(
        """
def test(a, b):
    return a + b
    """,
        "ret == 4 and pyname_a == 3",
        {"a": 3, "b": 1, "ret": 4},
    )


def test_if_case():
    check_solve(
        """
def test(r):
    while r > 1:
        r -= 1
    return r
    """,
        "pyname_r == 2",
        {"ret": 1, "r": 2, "r_1": 1},
    )


def test_loop_unrolling_case():
    check_solve(
        """
def print_all(count):
    while count > 0:
        count -= 1
        print(count)
    return count
    """,
        "pyname_count == 20",
        spotcheck({"ret": 0}),
        unroll=20,
    )


def test_insufficient_loop_case():
    check_solve(
        """
def print_all(count):
    while count > 0:
        count -= 1
        print(count)
    return count
    """,
        "pyname_count == 20",
        None,
    )


def test_empty_string():
    check_solve(
        """
def print_all(s):
    if s == '':
        ret = 1
    else:
        ret = 2
    return ret
    """,
        "ret == 1",
        {"ret": 1, "s": ""},
    )


def test_string_test_case():
    check_solve(
        """
def print_all(s):
    if s == 'a':
        ret = 1
    else:
        ret = 2
    return ret
    """,
        "ret == 1",
        {"ret": 1, "s": "a"},
    )


def merge(*dicts):
    merged = {}
    for d in dicts:
        merged.update(d)
    return merged


class spotcheck:
    def __init__(self, spots):
        self.spots = spots

    def check(self, actual):
        for k, v in self.spots.items():
            assert actual[k] == v
