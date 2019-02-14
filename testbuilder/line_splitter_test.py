from ast import parse
from functools import partial

from toolz import pipe

from .ast_to_ssa import ast_to_ssa
from .line_splitter import line_splitter


def check_lines(code, expected):
    _ast_to_ssa = partial(ast_to_ssa, 2, {})
    ssa = pipe(code.strip(), parse, _ast_to_ssa)
    print("ssa", ssa)
    actual = line_splitter(ssa)
    assert actual == expected


def test_basic_split():
    check_lines(
        """
def abc():
    return 42
    """,
        [2],
    )


def test_splitting_with_ignored_code():
    check_lines(
        """
def abc():
    42
    "werkjhg"
    abs(23)
        """,
        [4],
    )


def test_splitting_with_loop():
    check_lines(
        """
def example(i):
    while i != None:
        fish = i
        while fish != None:
            fish = fish.right
        i = i.left
    return i
        """,
        [3, 5, 6, 7],
    )
