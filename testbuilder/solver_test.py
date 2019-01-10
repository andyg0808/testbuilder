import ast

import z3

from . import ssa_basic_blocks as sbb
from .expression_builder import get_expression
from .solver import solve
from .type_builder import TypeBuilder
from .variable_expander import expand_variables

Registrar = TypeBuilder().wrappers().references().structures().build()


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
    testdata = get_expression(Registrar, -1, parse, depth=unroll)
    if conditions:
        condition_expression = expand_variables(conditions, Registrar)
        expression = sbb.TestData(
            name=testdata.name,
            source_text=testdata.source_text,
            free_variables=testdata.free_variables,
            expression=z3.And(testdata.expression, condition_expression),
        )
    else:
        expression = testdata
    print("expression", expression)
    res = solve(Registrar, expression)
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
        "",
        {"ret": 42, "r": False},
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
        "pyname_count == Any.Int(20)",
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
        spotcheck({"a": (3, 4)}),
    )


def test_store_mutation():
    check_solve(
        """
def test(a):
    a.left += 3
    return a.left
        """,
        "ret == Any.Int(2)",
        spotcheck({"a": (2, False)}),
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
