import z3  # type: ignore

from .variable_expander import expand_variables


def test_var_expand():
    assert z3.eq(z3.Int("a") + z3.IntVal(1), expand_variables("a + 1"))
    result = expand_variables("c == amphibian + 12398")
    assert z3.eq(z3.Int("c") == z3.Int("amphibian") + z3.IntVal(12398), result)
    assert z3.eq(z3.IntVal("1"), expand_variables("1"))


def test_include_z3():
    assert z3.eq(z3.BoolVal(True), expand_variables("z3.BoolVal(True)"))


def test_include_z3():
    assert z3.eq(z3.BoolVal(True), expand_variables("true"))


def test_alternate_sort():
    assert z3.eq(z3.Bool("pyname_r"), expand_variables("bpyname_r"))
    assert z3.eq(z3.String("pyname_r"), expand_variables("spyname_r"))
    assert z3.eq(z3.Int("pyname_r"), expand_variables("pyname_r"))


def test_logical_notation():
    assert z3.eq(
        z3.And(z3.BoolVal(True), z3.Or(z3.Not(z3.BoolVal(False)), z3.BoolVal(True))),
        expand_variables("true & (~false | true)"),
    )


def test_low_precedence_logical_notation():
    assert z3.eq(
        z3.And(
            z3.BoolVal(True),
            z3.Or(z3.Not(z3.BoolVal(False)), z3.BoolVal(True)),
            z3.BoolVal(True),
        ),
        expand_variables("true and (not false or true) and true"),
    )


def test_string_support():
    assert z3.eq(z3.StringVal("abc"), expand_variables("'abc'"))
