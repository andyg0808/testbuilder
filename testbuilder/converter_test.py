import ast
from typing import Optional

import z3

from .ast_builder import make_ast
from .converter import convert
from .variable_expander import expand_variables
from .z3_types import Any as AnyType, make_any

Bool = z3.BoolSort()
Int = z3.IntSort()


def conversion_assert(
    expected,
    code_string: Optional[str] = None,
    variables=None,
    expected_type=None,
    expected_constraint=None,
):
    if not variables:
        variables = {}
    if isinstance(expected, str):
        if code_string is None:
            code_string = expected
        expected = expand_variables(expected)
    code = ast.parse(code_string)
    if isinstance(code, ast.Module):
        assert len(code.body) == 1
        code = code.body[0]
    if isinstance(code, ast.Expr):
        # Code that's just an expression should be something we are really wanting to test
        code = code.value
    tree = make_ast(variables, code)
    if expected_constraint is not None:
        expected_constraint = expand_variables(expected_constraint)
    result = convert(tree).unwrap(expected_type, expected_constraint)
    print("expected", expected)
    print("actual", result)
    assert z3.eq(expected, result)


def test_int():
    conversion_assert("2")
    conversion_assert("3")


def test_string():
    # conversion_assert('String("abc")', '"abc"')
    # conversion_assert('String("def") + String("hjk")', '"def" + "hjk"')
    conversion_assert('"abc"')
    conversion_assert('"def" + "hjk"')


def test_add():
    conversion_assert("1 + 2")


def test_add_multiple():
    conversion_assert("4 + 3 + 1")


def test_subtract():
    conversion_assert("4 - 3")


def test_multiply():
    conversion_assert("4 * 3")


def test_divide():
    conversion_assert("4 / 3")


def test_lt():
    conversion_assert("4 < 3")


def test_lte():
    conversion_assert("4 <= 3")


def test_gt():
    conversion_assert("4 > 3")


def test_gte():
    conversion_assert("4 >= 3")


def test_eq():
    conversion_assert("4 == 4")


def test_bounding():
    expected = (z3.IntVal(1) < z3.IntVal(2)) < z3.IntVal(3)
    conversion_assert(expected, "1 < 2 < 3")


def test_bounding():
    expected = (
        (((z3.IntVal(1) < z3.IntVal(2)) < z3.IntVal(3)) > z3.IntVal(2)) > z3.IntVal(1)
    ) > -z3.IntVal(4)
    conversion_assert(expected, "1 < 2 < 3 > 2 > 1 > -4")


def test_and():
    conversion_assert(
        z3.And(z3.And(z3.BoolVal(True), z3.BoolVal(True)), z3.BoolVal(False)),
        "True and True and False",
    )


def test_or():
    conversion_assert(z3.Or(z3.BoolVal(False), z3.BoolVal(True)), "False or True")


def test_negative():
    conversion_assert("-1")


def test_return():
    print("expansion", type(expand_variables("ret == Any.Int(2)")))
    conversion_assert("ret == Any.Int(2)", "return 2")


def test_variable():
    conversion_assert(
        AnyType.i(make_any("pyname_a")),
        "a",
        expected_type=Int,
        expected_constraint="Any.is_Int(pyname_a)",
    )


def test_assignment():
    conversion_assert("pyname_a == Any.Int(1)", "a = 1")


def test_mutation():
    # Accesses: Nothing changes
    # First write: pyname_a; variables: None
    # First read: pyname_a; variables: 0
    # Second write: pyname_a_1; variables: 1
    # Second read: pyname_a_1; variables: 1
    # Third write: pyname_a_2; variables: 2
    conversion_assert("pyname_a == Any.Int(1)", "a = 1")
    conversion_assert(
        "And(pyname_a_1 == Any.Int(Any.i(pyname_a) + 1), Any.is_Int(pyname_a))",
        "a = a + 1",
        {"a": 0},
    )
    conversion_assert(
        "And(pyname_a_2 == Any.Int(Any.i(pyname_a_1) + 1), Any.is_Int(pyname_a_1))",
        "a = a + 1",
        {"a": 1},
    )
    conversion_assert(
        "And(pyname_a_3 == Any.Int(Any.i(pyname_a_2) + 1), Any.is_Int(pyname_a_2))",
        "a = a + 1",
        {"a": 2},
    )


def test_augmutation():
    # print(
    #     "expansion",
    #     expand_variables(
    #         "And(pyname_a_1 == Any.Int(Any.i(pyname_a) + 1), Any.is_Int(pyname_a))"
    #     ),
    # )
    # print("done expression")
    conversion_assert(
        "And(pyname_a_1 == Any.Int(Any.i(pyname_a) + 1), Any.is_Int(pyname_a))",
        "a += 1",
        {"a": 0},
    )
    conversion_assert(
        "And(pyname_a_2 == Any.Int(Any.i(pyname_a_1) + 1), Any.is_Int(pyname_a_1))",
        "a += 1",
        {"a": 1},
    )


def test_booleans():
    conversion_assert("true", "True", expected_type=Bool)
    conversion_assert("false", "False", expected_type=Bool)
