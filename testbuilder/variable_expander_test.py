import pytest

import z3

from . import z3_types as z3t
from .type_builder import TypeBuilder
from .variable_expander import expand_variables

Registrar = TypeBuilder().construct()


def test_var_expand():
    assert z3.eq(
        Registrar.anytype.i(Registrar.make_any("a")) + z3.IntVal(1),
        expand_variables("Any.i(a) + 1", Registrar),
    )
    result = expand_variables("c == Any.Int(Any.i(amphibian) + 12398)", Registrar)
    assert z3.eq(
        Registrar.make_any("c")
        == Registrar.anytype.Int(
            Registrar.anytype.i(Registrar.make_any("amphibian")) + z3.IntVal(12398)
        ),
        result,
    )
    assert z3.eq(z3.IntVal("1"), expand_variables("1", Registrar))


def test_include_z3():
    assert z3.eq(z3.BoolVal(True), expand_variables("z3.BoolVal(True)", Registrar))


def test_include_z3():
    assert z3.eq(z3.BoolVal(True), expand_variables("true", Registrar))


def test_logical_notation():
    assert z3.eq(
        z3.And(z3.BoolVal(True), z3.Or(z3.Not(z3.BoolVal(False)), z3.BoolVal(True))),
        expand_variables("true & (~false | true)", Registrar),
    )


def test_low_precedence_logical_notation():
    assert z3.eq(
        z3.And(
            z3.BoolVal(True),
            z3.Or(z3.Not(z3.BoolVal(False)), z3.BoolVal(True)),
            z3.BoolVal(True),
        ),
        expand_variables("true and (not false or true) and true", Registrar),
    )


def test_string_support():
    assert z3.eq(z3.StringVal("abc"), expand_variables("'abc'", Registrar))
