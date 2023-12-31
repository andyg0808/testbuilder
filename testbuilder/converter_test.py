import ast
from typing import Optional

import pytest

import z3

from . import ssa_basic_blocks as sbb
from .ast_to_ssa import ast_to_ssa
from .converter import ExpressionConverter, TupleError
from .ssa_repair import repair
from .store import Store
from .type_builder import TypeBuilder
from .type_manager import TypeManager
from .variable_expander import expand_variables
from .z3_types import diff_expression, print_diff

Registrar = TypeBuilder().wrappers().build()

Bool = z3.BoolSort()
Int = z3.IntSort()


def conversion_assert(
    expected,
    code_string: Optional[str] = None,
    variables=None,
    expected_type=None,
    expected_constraint=None,
    get_boolean=False,
):
    print("Starting variables", variables)
    if not variables:
        variables = {}
    if isinstance(expected, str):
        if code_string is None:
            code_string = expected
        expected = expand_variables(expected, registrar=Registrar)
    code = ast.parse(code_string)
    tree = ast_to_ssa(2, variables, code)
    # Make variable assignment counts sensible
    tree = repair(tree)
    assert isinstance(tree, sbb.Module)
    assert len(tree.functions) == 0
    tree = tree.code.end
    assert len(tree.parents) == 1
    tree = tree.parents[0]
    assert isinstance(tree, sbb.Code)
    assert len(tree.code) == 1
    tree = tree.code[0]
    if expected_constraint is not None:
        expected_constraint = expand_variables(expected_constraint, registrar=Registrar)
    result = ExpressionConverter(Registrar, TypeManager(), Store(Registrar))(tree)
    if get_boolean:
        assert result.is_bool(), "Expected boolean result!"
        result = result.to_expr()
    else:
        result = result.unwrap(expected_type, expected_constraint)
    print("expected", expected)
    print("actual", result)
    diff = diff_expression(expected, result)
    if diff is not None:
        print_diff(diff)
    assert z3.eq(expected, result)


def test_int():
    conversion_assert("2")
    conversion_assert("3")


def test_float():
    conversion_assert("z3.RealVal(3)", "3.0")


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
    conversion_assert("z3.ToReal(4) / z3.ToReal(3)", "4/3")
    conversion_assert("z3.ToReal(4) / z3.RealVal(3.0)", "4/3.0")
    conversion_assert("z3.RealVal(4) / z3.ToReal(3)", "4.0/3")
    conversion_assert("z3.RealVal(4) / z3.RealVal(3)", "4.0/3.0")


def test_mod():
    conversion_assert("5 % 3")


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


def test_var_eq():
    conversion_assert("pyname_a == pyname_b", "a == b")


def test_implicit_bool_negation():
    conversion_assert(
        "Not(Any.b(pyname_a))",
        "not a",
        expected_type=Bool,
        expected_constraint="Any.is_Bool(pyname_a)",
    )


def test_bounding():
    expected = z3.And(z3.IntVal(1) < z3.IntVal(2), z3.IntVal(2) < z3.IntVal(3))
    conversion_assert(expected, "1 < 2 < 3")


def test_bounding_2():
    # expected = (
    #     (((z3.IntVal(1) < z3.IntVal(2)), (z3.IntVal(2) < z3.IntVal(3)) > z3.IntVal(2)) > z3.IntVal(1)
    # ) > -z3.IntVal(4)
    expected = z3.And(
        z3.IntVal(1) < z3.IntVal(2),
        z3.IntVal(2) < z3.IntVal(3),
        z3.IntVal(3) > z3.IntVal(2),
        z3.IntVal(2) > z3.IntVal(1),
        z3.IntVal(1) > -z3.IntVal(4),
    )
    conversion_assert(expected, "1 < 2 < 3 > 2 > 1 > -4")


def test_and():
    # Simplification of boolean values during conversion means we only
    # get False at the end.
    conversion_assert(z3.BoolVal(False), "True and True and False")


def test_or():
    # As with `test_and`, simplification of boolean values during
    # conversion means we only get True at the end.
    conversion_assert(z3.BoolVal(True), "False or True")


def test_negative():
    conversion_assert("-1")


def test_return():
    print("expansion", type(expand_variables("ret == Any.Int(2)", Registrar)))
    conversion_assert("ret == Any.Int(2)", "return 2")


def test_variable():
    conversion_assert(
        Registrar.anytype.i(Registrar.make_any("pyname_a")),
        "a",
        expected_type=Int,
        expected_constraint="Any.is_Int(pyname_a)",
    )


def test_assignment():
    conversion_assert("pyname_a == Any.Int(1)", "a = 1")


def test_addition_to_variable():
    conversion_assert(
        "And(pyname_b == Any.Int(Any.i(pyname_a) + 1), Any.is_Int(pyname_a))",
        "b = a + 1",
    )


def test_equality_with_variable():
    conversion_assert(
        """Or(And(Any.i(pyname_a) != 32, Any.is_Int(pyname_a)),
              Any.is_Float(pyname_a),
              Any.is_Bool(pyname_a),
              Any.is_String(pyname_a))""",
        "a != 32",
        get_boolean=True,
    )


def test_mutation():
    # Accesses: Nothing changes
    # First write: pyname_a; variables: None
    # First read: pyname_a; variables: 0
    # Second write: pyname_a_1; variables: 1
    # Second read: pyname_a_1; variables: 1
    # Third write: pyname_a_2; variables: 2
    conversion_assert("pyname_a == Any.Int(1)", "a = 1")
    # conversion_assert(
    #     "And(pyname_a_1 == Any.Int(Any.i(pyname_a) + 1), Any.is_Int(pyname_a))",
    #     "a = a + 1",
    #     {"a": 0},
    # )
    # conversion_assert(
    #     "And(pyname_a_2 == Any.Int(Any.i(pyname_a_1) + 1), Any.is_Int(pyname_a_1))",
    #     "a = a + 1",
    #     {"a": 1},
    # )
    # conversion_assert(
    #     "And(pyname_a_3 == Any.Int(Any.i(pyname_a_2) + 1), Any.is_Int(pyname_a_2))",
    #     "a = a + 1",
    #     {"a": 2},
    # )


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
        # {"a": 0},
    )
    # conversion_assert(
    #     "And(pyname_a_2 == Any.Int(Any.i(pyname_a_1) + 1), Any.is_Int(pyname_a_1))",
    #     "a += 1",
    #     {"a": 1},
    # )


def test_booleans():
    conversion_assert("true", "True", expected_type=Bool)
    conversion_assert("false", "False", expected_type=Bool)


def test_fail_tuple():
    with pytest.raises(TupleError):
        conversion_assert("(1,2,3)")
