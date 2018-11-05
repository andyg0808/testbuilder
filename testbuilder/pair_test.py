import ast
from functools import partial

import pytest

import z3
from toolz import pipe

from .expression_builder import get_expression
from .variable_expander import expand_variables
from .z3_types import TypeBuilder, diff_expression, print_diff


def check_expression(
    code_string,
    expected,
    line=-1,
    simplify=False,
    write_tree="",
    depth: int = 1,
    overall=False,
):
    """
    Args:
        code_string: A string of code to create an expression for
        expected: The expected expression resulting from the string of code
        line: The line number on which to slice.
        simplify: Whether to run z3.simplify on the example and actual output
                  before comparing.
        write_tree: If nonempty, a filename to which to write the basic block
                    tree generated while converting the expression.
        depth: The loop unrolling depth to use
        overall: Whether to generate an expression which does not use a
                 particular slice of the code.

        The overall option forces the expression to include all exit points
        from the function. It still uses the line number to choose which code
        to include, but control structures will be included for all exit
        points. Currently does nothing.
    """
    builder = TypeBuilder()
    builder.wrappers().structures()
    Registrar = builder.build()

    if isinstance(expected, str):
        expected = expand_variables(expected, Registrar)
    _get_expression = partial(get_expression, Registrar, line, depth=depth)
    test_data = pipe(code_string.strip(), ast.parse, _get_expression)
    if test_data is None:
        expr = None
    else:
        expr = test_data.expression
    print("expected  ", expected)
    print("expression", expr)
    if simplify:
        expected = z3.simplify(expected)
        expr = z3.simplify(expr)
    if expected is None:
        assert expr is None
    else:
        diff = diff_expression(expected, expr)
        if diff != None:
            print_diff(diff)
        assert diff == None


@pytest.mark.xfail
def test_class():
    check_expression(
        """
class Pair:
    def __init__(self, left, right):
        self.left = left
        self.right = right
e = Pair(2, 3)
left = e.left
right = e.right
        """,
        """
        pyname_e == Any.Pair(Any.Int(2), Any.Int(3))\
        and pyname_left == Any.Pair_left(pyname_e)\
        and pyname_right == Any.Pair_right(pyname_e)
""",
    )