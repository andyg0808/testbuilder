import ast

import pytest
from astor import to_source

from .preprocessor import AutoPreprocessor, Preprocessor


def check_preprocess(program, expected, auto=False):
    parsed = ast.parse(program)
    if auto:
        preprocess = AutoPreprocessor(program, auto)
    else:
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


def test_preprocessing_stop():
    check_preprocess(
        """
#!/usr/bin/env python3
# Other comment
# NAME/RENAME: fishes -> goats
class Jedavu:
    def func(name):
        return name + fishes
# NAME/RENAME: name -> crabs
    """,
        """
class Jedavu:
    def func(name):
        return name + goats
""",
    )


def test_auto_preprocess():
    check_preprocess(
        """
a.first = 4
a.second = 5
a.rest = 5
        """,
        """
a.left = 4
a.right = 5
a.right = 5
""",
        auto=[
            ("ATTRNAME", "RENAME", "first -> left"),
            ("ATTRNAME", "RENAME", "second -> right"),
            ("ATTRNAME", "RENAME", "rest -> right"),
        ],
    )


def test_preprocess_subscript():
    check_preprocess(
        """
s[0] = 4
s[1] = 5
        """,
        """
s.left = 4
s.right = 5
        """,
        auto=[
            ("SUBSCRIPT", "PARIFY", "0 -> left"),
            ("SUBSCRIPT", "PARIFY", "1 -> right"),
        ],
    )


def test_preprocess_tuple():
    check_preprocess("val = (1, 2)", "val = Pair(1, 2)", auto=[("TUPLE", "PARIFY", "")])
