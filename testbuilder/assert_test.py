from .check_expression import ExpressionChecker

check_expression = ExpressionChecker(lambda b: b.wrappers().references().structures())


def test_assert():
    check_expression("assert x == 1", "Any.i(pyname_x) == 1 and Any.is_Int(pyname_x)")


def test_assert_slicing():
    check_expression(
        """
def example(a, b):
    assert a == 1
    return b
    """,
        "Any.i(pyname_a) == 1 and Any.is_Int(pyname_a) and ret == pyname_b",
    )
