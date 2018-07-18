import ast

from .var_collector import find_vars


def test_find_basic_vars():
    code = ast.parse(
        """
def testfunc(a, b):
    return a + b
"""
    )
    varlist = find_vars(code)
    assert varlist == ["a", "b"]


def test_find_vars_in_assignment():
    code = ast.parse(
        """
def testfunc(a, b):
    c, d = a + b
"""
    )
    varlist = find_vars(code)
    assert varlist == ["a", "b"]


def test_find_vars_in_class():
    code = ast.parse(
        """
class TestClass:
    def __init__(self):
        pass

    def meh_thod(i, j, k):
        return i * j * k
    """
    )

    varlist = find_vars(code)
    assert varlist == ["i", "j", "k"]


def test_find_vars_with_augmentation():
    code = ast.parse(
        """
def func():
    prod += 1
"""
    )

    varlist = find_vars(code)
    # This one's weird: we don't actually handle augmented assignment, but
    # because the variable on the left is used to produce the result, it's
    # correct.
    assert varlist == ["prod"]


def test_find_vars_with_annotation():
    code = ast.parse(
        """
def func():
    prod: int = j
"""
    )

    varlist = find_vars(code)
    assert varlist == ["j"]


def test_find_vars_declare_var():
    code = ast.parse(
        """
def func():
    prod: int
"""
    )

    varlist = find_vars(code)
    assert varlist == []


def test_find_vars_splat():
    code = ast.parse(
        """
def func(d):
    a, b, c = *d
"""
    )

    varlist = find_vars(code)
    assert varlist == ["d"]


def test_find_vars_subscript():
    code = ast.parse(
        """
def func(d):
    return d[21]
"""
    )

    varlist = find_vars(code)
    assert varlist == ["d"]


def test_find_vars_var_subscript():
    code = ast.parse(
        """
def func(d, e):
    return d[e]
"""
    )

    varlist = find_vars(code)
    assert varlist == ["d", "e"]


def test_find_vars_attribute():
    code = ast.parse(
        """
def func(d):
    return d.fish
"""
    )

    varlist = find_vars(code)
    assert varlist == ["d"]


def test_find_vars_return_list():
    code = ast.parse(
        """
def func(d, e, f):
    return [d, e]
"""
    )

    varlist = find_vars(code)
    assert varlist == ["d", "e"]


def test_find_vars_return_string():
    code = ast.parse(
        """
def func(d, e, f):
    return "abc"
"""
    )

    varlist = find_vars(code)
    assert varlist == []
