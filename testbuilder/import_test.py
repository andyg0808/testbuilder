from .check_expression import ExpressionChecker

check_expression = ExpressionChecker(lambda b: b.wrappers())


def test_basic_import():
    check_expression("import math", None)


def test_from_import():
    check_expression("from math import sin", None)


def test_import_as():
    check_expression("import math as m", None)
    check_expression("from math import sin as sine", None)
