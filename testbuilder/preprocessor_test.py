import ast

from astor import to_source

from .preprocessor import Preprocessor


def check_preprocess(program, expected):
    parsed = ast.parse(program)
    preprocess = Preprocessor(program)
    clean_actual = to_source(preprocess(parsed))
    clean_expected = to_source(ast.parse(expected))
    print("Expected", clean_expected)
    print("Actual", clean_actual)
    assert clean_expected == clean_actual


def test_basic_preprocess():
    check_preprocess(
        """
# NAME/RENAME: fishes -> frogs
fishes = 4
        """,
        """
frogs = 4
""",
    )


def test_deep_preprocess():
    check_preprocess(
        """
# NAME/RENAME: fishes -> frogs
class Dejavu:
    def func(name):
        name.fishes = 33
    return frogs

    def things(name):
        return name + fishes
        """,
        """
class Dejavu:
    def func(name):
        name.fishes = 33
    return frogs

    def things(name):
        return name + frogs
""",
    )


def test_attr_preprocess():
    check_preprocess(
        """
# ATTRNAME/RENAME: fishes -> frogs
class Dejavu:
    def func(name):
        name.fishes = 33
    return frogs

    def things(name):
        return name + fishes
        """,
        """
class Dejavu:
    def func(name):
        name.frogs = 33
    return frogs

    def things(name):
        return name + fishes
""",
    )


def test_both_preprocess():
    check_preprocess(
        """
# ATTRNAME/RENAME: fishes -> frogs
# NAME/RENAME: fishes -> goats
class Dejavu:
    def func(name):
        name.fishes = 33
    return frogs

    def things(name):
        return name + fishes
        """,
        """
class Dejavu:
    def func(name):
        name.frogs = 33
    return frogs

    def things(name):
        return name + goats
""",
    )
