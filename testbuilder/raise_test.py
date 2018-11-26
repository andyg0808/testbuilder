from .check_expression import ExpressionChecker

check_expression = ExpressionChecker()


def test_basic_raise():
    check_expression(
        """
raise RuntimeError()
    """,
        """
    """,
    )
