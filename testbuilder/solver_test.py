import ast
from pathlib import Path

import pytest

import dataclasses
import z3

from .expression_builder import get_expression
from .pair import Pair
from .solver import solve
from .type_builder import TypeBuilder
from .variable_expander import expand_variables

Registrar = TypeBuilder().construct()


def compare_values(expected, actual, actual_dict):
    if callable(expected):
        print("actual", actual)
        print("dict", actual_dict)
        print("expected", expected)
        result = expected(actual, actual_dict)
        print("result", result)
        assert result
    else:
        print("expected", expected)
        print("actual", actual)
        assert type(expected) == type(actual)
        assert expected == actual


def compare_dicts(actual, expected):
    if expected is None:
        assert actual is None
        return
    else:
        assert actual is not None
    keys = actual.keys() | expected.keys()
    for k in keys:
        compare_values(expected[k], actual[k], actual)


def check_solve(code, conditions, expected, unroll=1, slice=True):
    """
    Args:
        code (str): A string of source code to check
        conditions (str): Additional code establishing constraints
                          which should be added to the solver. This
                          allows some control over the solution which
                          is found.
        expected (dict): A dict of the expected values for each solver
                         variable.
    """
    parse = ast.parse(code)
    testdata = get_expression(
        Registrar, Path("<source>"), -1, parse, depth=unroll, slice=slice
    )
    if conditions:
        condition_expression = expand_variables(conditions, Registrar)
        expression = dataclasses.replace(
            testdata, expression=z3.And(testdata.expression, condition_expression)
        )
    else:
        expression = testdata
    print("expression", expression)
    res = solve(Registrar, expression)
    print(f"Solution: {res}")
    if isinstance(expected, spotcheck):
        expected.check(res)
    else:
        compare_dicts(res, expected)


class spotcheck:
    def __init__(self, spots):
        self.spots = spots

    def check(self, actual):
        for k, v in self.spots.items():
            compare_values(v, actual[k], actual)


def test_basic_solution():
    check_solve(
        """
def test(a):
    return a
    """,
        "ret == Any.Int(4)",
        {"a": 4, "ret": 4},
    )


def test_arithmetic_solution():
    check_solve(
        """
def test(a, b):
    return a + b
    """,
        "ret == Any.Int(4) and pyname_a == Any.Int(3)",
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
        "pyname_r == Any.Int(2)",
        {"ret": 1, "r": 2, "r_1": 1},
    )


def test_bool_force():
    check_solve(
        """
def test(r):
    if r == False:
        return 42
        """,
        None,
        {"ret": 42, "r": False},
    )


@pytest.mark.second
def test_loop_unrolling_case():
    check_solve(
        """
def print_all(count):
    while count > 0:
        count -= 1
        print(count)
    return count
    """,
        "pyname_count == Any.Int(10)",
        spotcheck({"ret": 0}),
        unroll=10,
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
        "pyname_count == Any.Int(20)",
        None,
    )


def test_empty_string():
    check_solve(
        """
def print_all(s_empty):
    if s_empty == '':
        ret = 1
    else:
        ret = 2
    return ret
    """,
        "ret == Any.Int(1)",
        {"ret": 1, "s_empty": ""},
    )


def test_string_test_case():
    check_solve(
        """
def print_all(s_thing):
    if s_thing == 'a':
        ret = 1
    else:
        ret = 2
    return ret
    """,
        "ret == Any.Int(1)",
        {"ret": 1, "s_thing": "a"},
    )


def test_dereference():
    check_solve(
        """
def test(a):
    if a.left == 3 and a.right == 4:
        return 22
        """,
        "ret == Any.Int(22)",
        spotcheck({"a": Pair(3, 4)}),
    )


def test_store_mutation():
    check_solve(
        """
def test(a):
    a.left += 3
    assert a.right == False
    return a.left
        """,
        "ret == Any.Int(2)",
        spotcheck({"a": Pair(-1, False)}),
    )


def test_solve_invalid_reference():
    check_solve(
        """
def test(a):
    return a
        """,
        "Any.is_Reference(pyname_a)",
        {"ret": None, "a": None},
    )


def test_solve_invalid_reference_with_store():
    check_solve(
        """
def example(a):
    b.left = 42
    return a
        """,
        "Any.is_Reference(pyname_a)",
        spotcheck(
            {"ret": lambda ret, d: d["a"] == ret, "a": lambda a, d: d["ret"] == a}
        ),
        slice=False,
    )


@pytest.mark.first
def test_solve_multilayer():
    check_solve(
        """
def example(a):
    a.left.right.left.left.right.right = 22
    if a.left.right.right.left.left:
        return a.left.right.right.left.left
    else:
        assert a.left.right.right.left.right == 454
        return a.left.right.right.left.right
        """,
        False,
        spotcheck({"ret": 454}),
        slice=False,
    )


def test_solve():
    check_solve(
        """
def example(a):
    a = Pair(1, 2)
    b = a
    a = Pair(3, 4)
    c = a.right
    return b.left
        """,
        None,
        spotcheck({"ret": 1, "c": 4}),
        slice=False,
    )


def test_solve_is_not_none():
    check_solve(
        """
def example(a):
    if a is None:
        return 4
    return 3
    """,
        None,
        spotcheck({"a": lambda a, d: a is not None}),
    )


def test_solve_is_none():
    check_solve(
        """
def example(a):
    if a is None:
        return 3
        """,
        None,
        spotcheck({"a": None}),
    )
