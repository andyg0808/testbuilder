from .check_expression import ExpressionChecker

check_expression = ExpressionChecker()


def test_basic_raise():
    check_expression(
        """
raise RuntimeError()
    """,
        None,
    )


def test_avoiding_raise():
    check_expression(
        """
if a < 23:
    raise RuntimeError()
else:
    b = a + 3
c = b * 34
    """,
        """
And(Not(Any.i(pyname_a) < 23), Any.is_Int(pyname_a)) \
and pyname_b == Any.Int(Any.i(pyname_a) + 3) \
and pyname_c == Any.Int(Any.i(pyname_b) * 34)
""",
    )
