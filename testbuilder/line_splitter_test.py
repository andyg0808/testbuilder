from ast import parse
from functools import partial

from toolz import pipe

from .ast_to_ssa import ast_to_ssa
from .line_splitter import LineSplitter


def check_lines(code, expected):
    _ast_to_ssa = partial(ast_to_ssa, 2, {})
    ssa = pipe(code.strip(), parse, _ast_to_ssa)
    print("ssa", ssa)
    actual = LineSplitter()(ssa)
    assert actual == expected


def test_basic_split():
    check_lines(
        """
def abc():
    return 42
    """,
        [2],
    )
