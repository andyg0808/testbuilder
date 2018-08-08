import ast
from pprint import pprint
from typing import Mapping, Sequence, Union

import pytest

from .slicing import Dependency, Slicer, Variable, take_slice

Expectations = Union[str, Mapping[str, str]]


def check_code(
    actual: str, expected: Sequence[str], expected_vars: Sequence[str] = None, line=-1
) -> None:
    code = ast.parse(actual.strip())
    s = take_slice(line, code)
    s.walk_tree()
    check_slice(expected, s, expected_vars)


def check_slice(
    expected: Sequence[str], actual: Dependency, expected_vars: Sequence[str] = None
):
    slice_list = actual.format_slice()
    # Skip variables, because we don't want to have to print them in the
    # expected.
    code_list = [s for s in slice_list if not isinstance(s, Variable)]
    assert slice_list[0].required
    for s in slice_list[1:]:
        assert not s.required
    print("Formatted code list")
    pprint([ast.dump(i.code) for i in code_list])
    print("Slice tree:")
    pprint(actual.walk_tree())
    check_code_list(code_list, expected)
    if expected_vars is not None:
        var_list = [s.code for s in slice_list if isinstance(s, Variable)]
        assert_bag(expected_vars, var_list)


def get_tree(prog):
    code = ast.parse(prog)
    return ast.dump(code.body[0])


def check_code_list(code: Sequence[Dependency], expected: Sequence[Expectations]):
    assert len(code) == len(expected)
    code = sorted(code, key=lambda x: x.lineno)
    for statement, expectation in zip(code, expected):
        statement_string = ast.dump(statement.code)
        if isinstance(expectation, tuple):
            cond, line = expectation
            expected_cond = get_tree(cond)
            actual_cond = statement.conditional
            current_cond = ast.dump(actual_cond[-1].code)
            assert expected_cond == current_cond
        else:
            line = expectation
        line_string = get_tree(line)
        assert line_string == statement_string


def assert_bag(expected, actual):
    assert set(expected) == set(actual)
    assert len(expected) == len(actual)


def test_variable_slice():
    code = ast.parse(
        """
def testfunc(a):
    return a
    """.strip()
    )
    slicer = Slicer(code)
    s = slicer.take_slice(2)
    expected = Variable("a", 1)
    assert expected == list(s.dependencies)[0]


def test_assign_slice_variables():
    code = ast.parse(
        """
def testfunc(a):
    b = a
    """.strip()
    )
    slicer = Slicer(code)
    s = slicer.take_slice(2)
    expected = Variable("a", 1)
    assert expected == list(s.dependencies)[0]


def test_slicer():
    code = """
def testfunc(a, b):
    return a + b
"""
    expected = ["return a + b"]
    check_code(code, expected, ["a", "b"])


def test_slicer_multiline():
    code = """
def testfunc(a, b):
    c = a + b
    d = a * b
    c = c + d
    d = d + 1
    return c >> d
    """
    expected = ["c = a + b", "d = a * b", "c = c + d", "d = d + 1", "return c >> d"]
    check_code(code, expected, ["a", "b"])


def test_slicer_conditional():
    code = """
def testfunc(a, b):
    if a < b:
        c = 42
    else:
        c = b
        
    return c
    """
    expected = ["a < b", "a < b", ("a < b", "c = 42"), ("a < b", "c = b"), "return c"]
    check_code(code, expected)


def test_slicer_cond2():
    code = """
def testfunc(a=2, b=4):
    a = 32
    if a < b:
        b = a
    if a < 42:
        c = 45
    return c + b
    """
    expected = [
        "a = 32",
        "a < b",
        ("a < b", "b = a"),
        "a < 42",
        ("a < 42", "c = 45"),
        "return c + b",
    ]
    check_code(code, expected)


def test_slicer_cond3():
    code = """
def testfunc():
    pass
    """

    expected = ["pass"]
    check_code(code, expected)


def test_slicer_funccall():
    code = """
def testfunc(b):
    return abs(b)
    """

    expected = ["return abs(b)"]
    check_code(code, expected)


def test_slicer_funccall2():
    code = """
def testfunc(f, b):
    return f(b)
    """

    expected = ["return f(b)"]
    check_code(code, expected)


def test_slicer_funccall3():
    code = """
def testfunc(f, b):
    mr = map(f, b)
    mr = map(lambda x: 2*x, mr)
    return mr
    """

    expected = ["mr = map(f, b)", "mr = map(lambda x: 2*x, mr)"]
    check_code(code, expected, line=3)


def test_slicer_while():
    code = """
def testfunc(b):
    while b < 24:
        b += 1
    return b
    """

    expected = ["b < 24", ("b < 24", "b += 1"), "return b"]
    check_code(code, expected, line=4)


def test_slicer_annotated_assign():
    code = """
def testfunc(b: int):
    fish: int = b + 1
    return fish
    """

    expected = ["fish: int = b + 1", "return fish"]
    check_code(code, expected)


def test_slicer_unwritten_annassign():
    code = """
def testfunc(b: int):
    fish: int
    return fish
    """

    expected = ["return fish"]
    check_code(code, expected)


def test_variable_listing():
    code = """
if x < y:
    r = x
    x = 4
else:
    r = y
    y = 2
z = r + x + y
    """
    expected = [
        "x < y",
        "x < y",
        ("x < y", "r = x"),
        ("x < y", "x = 4"),
        ("x < y", "r = y"),
        ("x < y", "y = 2"),
        "z = r + x + y",
    ]
    check_code(code, expected, ["x", "y"])


def test_nested_ifs():
    code = """
def trimin(x, y, z):
    if x < y:
        if z < x:
            r = z
        else:
            r = x
    else:
        if z < y:
            r = z
        else:
            r = y
    return r
    """
    expected = [
        "x < y",
        "x < y",
        ("x < y", "z < x"),
        ("x < y", "z < x"),
        ("z < x", "r = z"),
        ("z < x", "r = x"),
        ("x < y", "z < y"),
        ("x < y", "z < y"),
        ("z < y", "r = z"),
        ("z < y", "r = y"),
        "return r",
    ]
    check_code(code, expected, ["x", "y", "z"])


def test_returning_from_if():
    code = """
def returnthings(a, b):
    if 4 < 3:
        return a
    else:
        return b
    """
    expected = ["4 < 3", ("4 < 3", "return a")]
    check_code(code, expected, line=3)

    expected = ["4 < 3", ("4 < 3", "return b")]
    check_code(code, expected, line=5)


def test_all_vars():
    code = ast.parse(
        """
a = 0
if x < 1:
    a = 1
return a
    """.strip()
    )
    s = take_slice(-1, code)
    assert_bag([x.lineno for x in s.dependencies], [1, 3])


def test_all_vars2():
    code = ast.parse(
        """
a = 0
if x < 1:
    x = 1
else:
    x = 2
return a
    """.strip()
    )
    s = take_slice(-1, code)
    assert_bag([x.lineno for x in s.dependencies], [1])


def test_forked_mutation():
    code = """
a = 1
if a < 3:
    a = a + 2
else:
    a = a - 3
return a
    """
    expected = [
        "a = 1",
        "a < 3",
        "a < 3",
        ("a < 3", "a = a + 2"),
        ("a < 3", "a = a - 3"),
        "return a",
    ]
    check_code(code, expected)


def test_return_in_loop():
    check_code(
        """
def return_loop(i):
    while i > 0:
        return 2
    return 1
            """,
        ["i > 0", ("i > 0", "return 2")],
        ["i"],
        line=3,
    )


def test_slice_invalid_line():
    s = Slicer(
        ast.parse(
            """
a = 1

b = 2
    """.strip()
        )
    )
    assert 2 not in s


def test_slice_after_return():
    s = Slicer(
        ast.parse(
            """
return 1

a + 1
    """.strip()
        )
    )
    assert 3 not in s


@pytest.mark.skip(remark="This will need to be done eventually")
def test_slice_for_loop():
    check_code(
        """
for i in range(10):
    return i
    """,
        ["return i"],
    )
