import ast

import pytest

import z3

from .expression_builder import ExpressionBuilder, get_expression
from .slicing import take_slice
from .test_utils import write_dot
from .variable_expander import expand_variables

# def test_conditional_index():
#    assert conditional_diff_index([1,2,3], [1,2,3,4]) == 3
#    assert conditional_diff_index([1,2,3,4], [1,2,3]) == 3
#    assert conditional_diff_index([1,1,3,4], [1,2,3]) == 1
#    assert conditional_diff_index([1,4,5], [1,4,3]) == 2


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
    if isinstance(expected, str):
        expected = expand_variables(expected)
    expr = get_expression(ast.parse(code_string.strip()), line, depth)
    print("expected", expected)
    print("expr", expr)
    if simplify:
        expected = z3.simplify(expected)
        expr = z3.simplify(expr)
    if expected is None:
        assert expr is None
    else:
        assert z3.eq(expected, expr)


def test_constant():
    check_expression(
        """
def one():
    return 1
    """,
        "ret == 1",
    )


def test_constant_expression():
    check_expression(
        """
def three():
    return 1 + 2
    """,
        "ret == 1 + 2",
    )


def test_variable_expression():
    check_expression(
        """
def athing(a):
    return a
    """,
        "ret == pyname_a",
    )


def test_variable_use():
    check_expression(
        """
def twothings(a, b):
    return a + b
    """,
        "ret == pyname_a + pyname_b",
    )


def test_multiple_lines():
    check_expression(
        """
a = 1
return a + 1
    """,
        "pyname_a == 1 and ret == pyname_a + 1",
    )


def test_multiple_dependencies():
    """
    This tests the case where a line depends on multiple other lines, but there
    is no if-fork involved.
    """
    check_expression(
        """
def multiple_deps(a, b):
    c = a
    d = b
    return c + d
    """,
        "pyname_c == pyname_a and pyname_d == pyname_b and ret == pyname_c + pyname_d",
    )


def test_primitive_mutation():
    check_expression(
        """
a = 1
a = 2
    """,
        "pyname_a == 2",
    )


def test_difficult_mutation():
    check_expression(
        """
a = 1
a = a + 1
    """,
        "pyname_a == 1 and pyname_a_1 == pyname_a + 1",
    )


def test_forked_mutation():
    check_expression(
        """
c = 0
if a > b:
    c += a
else:
    c += b
return c
    """,
        """
pyname_c == 0 and \
(((pyname_a > pyname_b) and pyname_c_1 == pyname_c + pyname_a) or \
(Not(pyname_a > pyname_b) and pyname_c_1 == pyname_c + pyname_b)) and \
ret == pyname_c_1
""",
    )


def test_single_sided_forked_mutation():
    check_expression(
        """
if a > b:
    c = 3
else:
    d = 4
return c
    """,
        """
((pyname_a > pyname_b) and pyname_c == 3 \
 or \
 Not(pyname_a > pyname_b)) \
and ret == pyname_c
    """,
    )


def test_mutation_of_args():
    check_expression(
        """
def tester(a):
    a += 2
    return a
    """,
        "pyname_a_1 == pyname_a + 2 and ret == pyname_a_1",
    )


def test_mutation_of_inferred_variable():
    # When the slicer can't find a variable definition, it infers a variable.
    # Thus, mutation on random variables from an expression works.
    check_expression("a += 1", "pyname_a_1 == pyname_a + 1")


def test_basic_if_expression():
    # This one behaves weird because when we slice on the last line, we only
    # pull the false-condition parts.
    check_expression(
        """
def things(a, b):
    if 4 < 3:
        return a
    else:
        return b
""",
        """
Not(4 < 3) and ret == pyname_b
""",
    )


def test_funky():
    check_expression(
        """
c = 3
if a < b:
    c = 4
else:
    pass
return c
    """,
        """
    pyname_c == 3 and \
    (pyname_a < pyname_b and pyname_c_1 == 4 or \
     (Not(pyname_a < pyname_b) and pyname_c_1 == pyname_c)) \
    and ret == pyname_c_1""",
    )


def test_get_if_expression():
    check_expression(
        """
def things(a, b):
    if 4 < 3:
        c = a + 2
    else:
        c = a + 3
    return c + b
    """,
        """
((4 < 3 and pyname_c == pyname_a + 2) \
or \
(not (4 < 3) and pyname_c == pyname_a + 3)) and \
ret == pyname_c + pyname_b
    """,
    )


def test_nested_if_expressions():
    check_expression(
        """
def things(a, b, c):
    if a < b:
        if c < a:
            return c
        else:
            return a
    else:
        if c < b:
            return c
        else:
            return b
            """,
        """
And(Not(pyname_a < pyname_b), Not(pyname_c < pyname_b), ret == pyname_b)
            """,
    )


def test_get_while_expression():
    check_expression(
        """
def things(a, b):
    while a > 1:
        a -= 1
    return a
    """,
        """
(pyname_a_1 == pyname_a or \
 pyname_a > 1 and pyname_a_1 == pyname_a - 1) and Not(pyname_a_1 > 1) and \
ret == pyname_a_1
    """,
    )


def test_while_expression_depth():
    check_expression(
        """
def things(a, b):
    while a > 1:
        a -= 1
    return a
    """,
        """
((pyname_a_2 == pyname_a) or \
 (pyname_a > 1 and pyname_a_1 == pyname_a - 1 \
  and pyname_a_2 == pyname_a_1) or \
 (pyname_a > 1 and pyname_a_1 == pyname_a - 1 and \
  pyname_a_1 > 1 and pyname_a_2 == pyname_a_1 - 1)) and Not(pyname_a_2 > 1) \
  and ret == pyname_a_2
    """,
        depth=2,
    )


def test_while_with_if():
    check_expression(
        """
def things(a, b):
    while a > 1:
        if b > 1:
            a -= b
        else:
            a += b
    return a
    """,
        """
((pyname_a_1 == pyname_a) or \
 (pyname_a > 1 and \
  (pyname_b > 1 and pyname_a_1 == pyname_a - pyname_b or \
   Not(pyname_b > 1) and pyname_a_1 == pyname_a + pyname_b) \
  )) and Not(pyname_a_1 > 1) and \
ret == pyname_a_1
    """,
    )


def test_nested_whiles():
    check_expression(
        """
def tester(a, b):
    while a > 1:
        while b > 1:
            b -= 1
        a = b
    return a
    """,
        """
    (pyname_a_1 == pyname_a and pyname_b_1 == pyname_b or \
     (pyname_a > 1 and \
      (pyname_b_1 == pyname_b or \
       pyname_b > 1 and pyname_b_1 == pyname_b - 1) and Not(pyname_b_1 > 1) and \
      pyname_a_1 == pyname_b_1)) and Not(pyname_a_1 > 1) and \
    ret == pyname_a_1
    """,
    )


def test_falsy_number():
    check_expression(
        """
def test(i):
    if i:
        return 1
    else:
        return 2
    """,
        """
    Not(pyname_i == 0) and ret == 2
    """,
    )


def test_falsy_number_while():
    check_expression(
        """
def test(i):
    while i:
        i -= 1
    return i
    """,
        """
    (pyname_i_1 == pyname_i or \
     pyname_i == 0 and pyname_i_1 == pyname_i - 1) and Not(pyname_i_1 == 0) and \
    ret == pyname_i_1
    """,
    )


def test_return_in_loop():
    check_expression(
        """
def test(i):
    while i > 0:
        return 2
    return 1
    """,
        "pyname_i > 0 and ret == 2",
        line=3,
        # depth=22,
        depth=2,
    )


def test_skip_returning_loop():
    check_expression(
        """
def test(i):
    while i > 0:
        return 1
    return i
    """,
        "Not(pyname_i > 0) and ret == pyname_i",
        depth=22,
    )


def test_sliced_conditional():
    check_expression(
        """
def test(i):
    if i < 8:
        j = 1
    return 2
    """,
        "ret == 2",
    )


def test_sliced_dependent_conditional():
    check_expression(
        """
def test(i):
    if i < 8:
        j = 1
    return i
    """,
        "ret == pyname_i",
    )


def test_sliced_while():
    check_expression(
        """
def test(i):
    while i < 5:
        j = 1
    return 2
    """,
        "ret == 2",
    )


def test_sliced_dependent_while():
    check_expression(
        """
def test(i):
    while i < 5:
        j = 1
    return i
    """,
        "ret == pyname_i",
    )


def test_conditional_return():
    check_expression(
        """
def test(i):
    if i < 8:
        if i < 2:
            return 1
    return 2
    """,
        "Or(pyname_i < 8 and Not(pyname_i < 2), Not(pyname_i < 8)) and ret == 2",
    )


def test_basic_conditional_return():
    check_expression(
        """
def test(i):
    if i > 8:
        return i
    return i
    """,
        "Not(pyname_i > 8) and ret == pyname_i",
    )


@pytest.mark.skip()
def test_avoid_infinite_loop():
    # We can't actually check for termination in all cases (thanks halting
    # problem!), but it would be nice if we could at least avoid running loops
    # which our checker can't confirm exit. To do this, we probably need to
    # stop slicing code.
    check_expression(
        """
def test(i):
    j = i
    while j > 1:
        j += 1
    return i
    """,
        "Not(i > 1) and ret == pyname_i",
    )


def test_conditional_else_return():
    check_expression(
        """
def test(i):
    if i < 8:
        if i < 2:
            i += 1
        else:
            return 1
    return 2
    """,
        "Or(pyname_i < 8 and pyname_i < 2, Not(pyname_i < 8)) and ret == 2",
    )


def test_skip_nondepend_returning_loop():
    check_expression(
        """
def test(i):
    while i > 0:
        return 1
    return 2
    """,
        "Not(pyname_i > 0) and ret == 2",
    )


@pytest.mark.skip
def test_conditional_return_in_loop():
    code = """
def test(i):
    while i > 0:
        if i == 2:
            return 2
        else:
            i -= 1
    return i
    """
    check_expression(code, "pyname_i > 0 and pyname_i == 2 and ret == 2", line=4)


@pytest.mark.skip
def test_conditional_break_in_loop():
    code = """
def test(u):
    while u > 1:
        u -= 1
        if u < 20:
            break
    return u
    """


@pytest.mark.skip
def test_break_in_loop():
    code = """
def test(i):
    while i > 1:
        break
    return i
    """


def test_return_halfway():
    code = """
    def test(i):
        i += 1
        return i
        i += 3
        return i
        """

    check_expression(code, "pyname_i_1 == pyname_i + 1 and ret == pyname_i_1", line=3)
    check_expression(code, None, line=5)


# Get returns to shortcircuit
def test_return_dependent_halfway():
    code = """
def test(i):
    i += 1
    return i
    i += 3
    return 0
    """
    check_expression(code, "pyname_i_1 == pyname_i + 1 and ret == pyname_i_1")
    check_expression(code, None, line=5)


def test_return_independent_halfway():
    code = """
def test():
    i = 1 + 2
    return i
    return 0
    """
    check_expression(code, "pyname_i == 1 + 2 and ret == pyname_i", line=3)
    check_expression(code, None, line=4)


def test_string_equality():
    check_expression(
        """
def test(s: str):
    if s == "win":
        res = 1
    else:
        res = 0
    return res
    """,
        """
    (spyname_s == "win" and pyname_res == 1 or \
    Not(spyname_s == "win") and pyname_res == 0) and \
    ret == pyname_res
    """,
    )


@pytest.mark.xfail
def test_string_length():
    check_expression(
        """
def test(s: str):
    if len(s) > 2:
        res = 1
    else:
        res = 0
    return res
    """,
        """
    (Length("s") > 2 and pyname_res == 1 or \
    Not(Length("s") > 2) and pyname_res == 0) and \
    ret == pyname_res
    """,
    )


@pytest.mark.xfail
def test_side_effect_while():
    check_expression(
        """
def tester(count):
    while count > 0:
        count -= 1
        print(count)
""",
        """
    And(Not(pyname_count > 0), True) or \
    And(pyname_count > 0, pyname_count_1 == pyname_count - 1, True, \
        Not(pyname_count_1 > 0))
""",
        overall=True,
    )


@pytest.mark.skip
def test_flow_dependent_type():
    check_expression(
        """
def tester(b):
    if b:
        ret = 1
    else:
        ret = "a"

    return ret + 1
""",
        "",
    )

    # After an example in canon2005
    # This function will crash if passed False (because it tries to add a number to
    # a string). This needs to be discovered!
