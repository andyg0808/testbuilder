import pytest

from .check_expression import ExpressionChecker

check_expression = ExpressionChecker(lambda b: b.wrappers())


def test_basic_call():
    # TODO: Handle calls correctly
    # What about recursion?
    check_expression("abs(i)", "true")


def test_negative_slice():
    check_expression(
        """
x = 24
y = 25
        """,
        "pyname_x == Any.Int(24)",
        line=-2,
    )


def test_multiplication():
    check_expression(
        "return i * 2", "ret == Any.Int(Any.i(pyname_i) * 2) and Any.is_Int(pyname_i)"
    )


def test_gte():
    check_expression(
        "return i >= 4",
        "ret == Any.Bool(Any.i(pyname_i) >= 4) and Any.is_Int(pyname_i)",
    )


def test_neq():
    check_expression(
        "i != 4",
        """
        Or(
          And(Any.i(pyname_i) != 4,
              Any.is_Int(pyname_i)),
          Any.is_Bool(pyname_i),
          Any.is_String(pyname_i)
        )
        """,
    )


def test_lte():
    check_expression(
        "return i <= 4",
        "ret == Any.Bool(Any.i(pyname_i) <= 4) and Any.is_Int(pyname_i)",
    )


def test_div():
    check_expression(
        "return i / 3", "ret == Any.Int(Any.i(pyname_i) / 3) and Any.is_Int(pyname_i)"
    )


@pytest.mark.skip
def test_is_not():
    check_expression("i is not j", "id(pyname_i) != id(pyname_j)")


def test_constant():
    check_expression(
        """
def one():
    return 1
    """,
        "ret == Any.Int(1)",
    )


def test_constant_expression():
    check_expression(
        """
def three():
    return 1 + 2
    """,
        "ret == Any.Int(1 + 2)",
    )


def test_variable_expression():
    # TODO: Would be nice if this was clever and didn't break Any up until needed
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
        """
ret == Any.Int(Any.i(pyname_a) + Any.i(pyname_b)) and \
 Any.is_Int(pyname_a) and Any.is_Int(pyname_b) or \
ret == Any.String(z3.Concat(Any.s(pyname_a), Any.s(pyname_b))) and \
 Any.is_String(pyname_a) and Any.is_String(pyname_b)
""",
    )


def test_multiple_lines():
    check_expression(
        """
a = 1
return a + 1
    """,
        """
pyname_a == Any.Int(1)\
 and ret == Any.Int(Any.i(pyname_a) + 1)
""",
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
        """
pyname_c == pyname_a and \
pyname_d == pyname_b and \
Or(ret == Any.Int(Any.i(pyname_c) + Any.i(pyname_d)) and
    Any.is_Int(pyname_c) and
    Any.is_Int(pyname_d),
   ret == Any.String(Concat(Any.s(pyname_c), Any.s(pyname_d))) and
    Any.is_String(pyname_c)
    and Any.is_String(pyname_d))
""",
    )


def test_primitive_mutation():
    check_expression(
        """
a = 1
a = 2
    """,
        "pyname_a == Any.Int(2)",
    )


def test_difficult_mutation():
    check_expression(
        """
a = 1
a = a + 1
    """,
        """
pyname_a == Any.Int(1) and \
pyname_a_1 == Any.Int(Any.i(pyname_a) + 1)
""",
    )


@pytest.mark.skip
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
        (((Any.i(pyname_a) > Any.i(pyname_b)) and \
          pyname_c_1 == Any.i(pyname_c) + Any.i(pyname_a)) or \
        (Not(Any.i(pyname_a) > Any.i(pyname_b)) and \
     pyname_c_1 == Any.Int(Any.i(pyname_c) + Any.i(pyname_b)))) and \
ret == pyname_c_1
""",
    )


@pytest.mark.skip
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
        """
pyname_a_1 == Any.Int(Any.i(pyname_a) + 2) and \
Any.is_Int(pyname_a) and \
ret == pyname_a_1
""",
    )


@pytest.mark.skip
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
    pyname_c == Any.Int(3) and \
        (Any.i(pyname_a) < Any.i(pyname_b) and
        Any.is_Int(pyname_a) and Any.is_Int(pyname_b) \
        and pyname_c_1 == Any.Int(4) \
    or \
        Not(Any.i(pyname_a) < Any.i(pyname_b)) and \
            Any.is_Int(pyname_a) and Any.is_Int(pyname_b) \
    and pyname_c_1 == pyname_c) \
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
        ((4 < 3 and \
          pyname_c == Any.Int(Any.i(pyname_a) + 2) and \
              Any.is_Int(pyname_a)) \
or \
        (not (4 < 3) and \
         pyname_c == Any.Int(Any.i(pyname_a) + 3) and \
             Any.is_Int(pyname_a))) and \
    ret == Any.Int(Any.i(pyname_c) + Any.i(pyname_b)) and \
    Any.is_Int(pyname_b)
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
        And(Not(Any.i(pyname_a) < Any.i(pyname_b)),
                Any.is_Int(pyname_a), Any.is_Int(pyname_b),
            Not(Any.i(pyname_c) < Any.i(pyname_b)),
                Any.is_Int(pyname_c),
            ret == pyname_b)
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
And(pyname_a_1 == pyname_a or \
        And(Any.i(pyname_a) > 1, Any.is_Int(pyname_a),
        pyname_a_1 == Any.Int(Any.i(pyname_a) - 1)), \
        Not(Any.i(pyname_a_1) > 1), Any.is_Int(pyname_a_1),
ret == pyname_a_1)
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
        (Any.i(pyname_a) > 1 and Any.is_Int(pyname_a) \
         and pyname_a_1 == Any.Int(Any.i(pyname_a) - 1) \
         and pyname_a_2 == pyname_a_1) or \
        (Any.i(pyname_a) > 1 and Any.is_Int(pyname_a) \
         and pyname_a_1 == Any.Int(Any.i(pyname_a) - 1)\
        and Any.i(pyname_a_1) > 1\
        and pyname_a_2 == Any.Int(Any.i(pyname_a_1) - 1)))\
        and Not(Any.i(pyname_a_2) > 1) and Any.is_Int(pyname_a_2) \
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
Or(pyname_a_1 == pyname_a, \
   And(Any.i(pyname_a) > 1, Any.is_Int(pyname_a),
        Or(Any.i(pyname_b) > 1 and Any.is_Int(pyname_b)
           and pyname_a_1 == Any.Int(Any.i(pyname_a) - Any.i(pyname_b)),
          Not(Any.i(pyname_b) > 1) and Any.is_Int(pyname_b)
           and pyname_a_1 == Any.Int(Any.i(pyname_a) + Any.i(pyname_b)))))\
and Not(Any.i(pyname_a_1) > 1) and Any.is_Int(pyname_a_1)\
and ret == pyname_a_1
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
    (pyname_a_1 == pyname_a or \
        (Any.i(pyname_a) > 1 and Any.is_Int(pyname_a) and \
      (pyname_b_1 == pyname_b or \
        Any.i(pyname_b) > 1 and Any.is_Int(pyname_b) and \
         pyname_b_1 == Any.Int(Any.i(pyname_b) - 1)) and \
        Not(Any.i(pyname_b_1) > 1) and Any.is_Int(pyname_b_1) and \
        pyname_a_1 == pyname_b_1)) and \
        Not(Any.i(pyname_a_1) > 1) and Any.is_Int(pyname_a_1) and \
    ret == pyname_a_1
    """,
    )


def test_return_before_conditional():
    check_expression(
        """
def test(i):
    i += 1
    if i < 10:
        i += 2
    else:
        i -= 10
    return i
        """,
        "And(pyname_i_1 == Any.Int(Any.i(pyname_i) + 1), Any.is_Int(pyname_i))",
        line=2,
    )


def test_falsy_value():
    check_expression(
        """
def test(i):
    if i:
        return 1
    else:
        return 2
    """,
        """
        Or(And(Not(Any.i(pyname_i) != 0), Any.is_Int(pyname_i)),
           And(Not(Any.b(pyname_i)), Any.is_Bool(pyname_i)),
           And(Not(Length(Any.s(pyname_i)) != 0), Any.is_String(pyname_i)))\
        and ret == Any.Int(2)
    """,
    )


@pytest.mark.skip
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
        "Any.i(pyname_i) > 0 and Any.is_Int(pyname_i) and ret == Any.Int(2)",
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
        "Not(Any.i(pyname_i) > 0) and Any.is_Int(pyname_i) and ret == pyname_i",
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
        "ret == Any.Int(2)",
    )


def test_slice_on_condition():
    check_expression(
        """
def test(i):
    i += 1
    if i < 8:
        i += 4
    else:
        i += 1
    return i
        """,
        """And(pyname_i_1 == Any.Int(Any.i(pyname_i) + 1),
               Any.is_Int(pyname_i))""",
        line=2,
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
        "Not(Any.i(pyname_i) < 5) and Any.is_Int(pyname_i) and ret == Any.Int(2)",
    )


def test_sliced_dependent_while():
    check_expression(
        """
def test(i):
    while i < 5:
        j = 1
    return i
    """,
        """And(Not(Any.i(pyname_i) < 5), Any.is_Int(pyname_i),
           ret == pyname_i)""",
    )


def test_uninteresting_dependent_while():
    # This case is where the `while` can't infinite loop, so the code
    # below it shouldn't be controlled by it at all. But proving that
    # seems too complicated, so for now we're allowing it to be
    # rendered.
    check_expression(
        """
def test(i):
    j = 5
    while j > 0:
        j -= 1
    return i
    """,
        """
        And(pyname_j == Any.Int(5),
        Or(pyname_j_1 == pyname_j,
           And(Any.i(pyname_j) > 0,
               pyname_j_1 == Any.Int(Any.i(pyname_j) - 1))),
        Not(Any.i(pyname_j_1) > 0),
        ret == pyname_i)
        """,
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
        """Or(And(Any.i(pyname_i) < 8, Any.is_Int(pyname_i),
               Not(Any.i(pyname_i) < 2)),
              And(Not(Any.i(pyname_i) < 8), Any.is_Int(pyname_i)))\
           and ret == Any.Int(2)""",
    )


def test_basic_conditional_return():
    check_expression(
        """
def test(i):
    if i > 8:
        return i
    return i
    """,
        "And(Not(Any.i(pyname_i) > 8), Any.is_Int(pyname_i), ret == pyname_i)",
    )


def test_multiple_assignment_filtering():
    check_expression(
        """
def test(i):
    if i < 10:
        i = 3
        i = 4
        i = 5
    else:
        return 1
    return 4
        """,
        "And(Any.i(pyname_i) < 10, Any.is_Int(pyname_i), ret == Any.Int(4))",
    )


def test_desired_conditional_return():
    check_expression(
        """
def test(i):
    if i > 8:
        return i
    return i
    """,
        "And(Any.i(pyname_i) > 8, Any.is_Int(pyname_i), ret == pyname_i)",
        line=3,
    )


@pytest.mark.skip()
def test_avoid_infinite_loop():
    # We can't actually check for termination in all cases (thanks
    # halting problem!), but it would be nice if we could at least
    # avoid running loops which our checker can't confirm exit. We
    # probably will need to track dependencies through loop
    # conditionals for this.
    check_expression(
        """
def test(i):
    j = i
    while j > 1:
        j += 1
    return i
    """,
        "pyname_j == pyname_i and Not(pyname_j > 1) and ret == pyname_i",
    )


@pytest.mark.skip
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
        "And(Not(Any.i(pyname_i) > 0), Any.is_Int(pyname_i), ret == Any.Int(2))",
    )


def test_conditional_return_in_loop():
    check_expression(
        """
def test(i):
    while i > 0:
        if i == 2:
            return 2
        else:
            i -= 1
    return i
    """,
        """
        And(Any.i(pyname_i) > 0, Any.is_Int(pyname_i),
        Any.i(pyname_i) == 2,
        ret == Any.Int(2))""",
        line=4,
    )


@pytest.mark.skip
def test_desired_loop():
    check_expression(
        """
def test(i):
    while i > 0:
        i -= 1
    return i
    """,
        "pyname_i > 0 and pyname_i_1 == pyname_i - 1",
        line=3,
    )


@pytest.mark.skip
def test_avoid_simple_infinite_loop():
    check_expression(
        """
def test(i):
    while i > 1:
        pass
    return i
    """,
        "Or(true, pyname_i > 1, pyname_i > 1 and pyname_i > 1)\
         and Not(pyname_i > 1) and ret == pyname_i",
    )


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

    check_expression(
        code,
        """
    And(pyname_i_1 == Any.Int(Any.i(pyname_i) + 1), Any.is_Int(pyname_i),
        ret == pyname_i_1)
    """,
        line=3,
    )
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
    check_expression(
        code,
        """
    And(pyname_i_1 == Any.Int(Any.i(pyname_i) + 1), Any.is_Int(pyname_i),
        ret == pyname_i_1)
    """,
    )
    check_expression(code, None, line=5)


def test_return_independent_halfway():
    code = """
def test():
    i = 1 + 2
    return i
    return 0
    """
    check_expression(
        code,
        """
    pyname_i == Any.Int(1 + 2) and ret == pyname_i
    """,
        line=3,
    )
    check_expression(code, None, line=4)


def test_string_equality():
    check_expression(
        """
def test(S_text: str):
    if S_text == "win":
        res = 1
    else:
        res = 0
    return res
    """,
        """
Or(And(Any.s(spyname_S_text) == "win", Any.is_String(spyname_S_text),
    pyname_res == Any.Int(1)),
   Or(Any.is_Int(spyname_S_text),
      Any.is_Bool(spyname_S_text),
      And(Not(Any.s(spyname_S_text) == "win"),
          Any.is_String(spyname_S_text)))\
    and pyname_res == Any.Int(0))\
and ret == pyname_res
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


def test_ignorable_conditional():
    check_expression(
        """
def test(i, j):
    if j > 4:
        j += 4
    else:
        j += 8
    return i
        """,
        "ret == pyname_i",
    )


@pytest.mark.skip
def test_affecting_conditional():
    check_expression(
        """
def test(i, j):
    j += 4
    if j > 3:
        i += 2
    else:
        i += 3
    return i
        """,
        """
        And(pyname_j_1 == pyname_j + 4,
        Or(    pyname_j_1 > 3  and pyname_i_1 == pyname_i + 2,
           Not(pyname_j_1 > 3) and pyname_i_1 == pyname_i + 3),
        ret == pyname_i_1)
        """,
    )


def test_boolean_parameter():
    check_expression(
        """
def test(doit):
    if doit == True:
        ret = 4
    else:
        ret = 5
    return ret
        """,
        """
And(
    And(Any.b(pyname_doit) == true, Any.is_Bool(pyname_doit),
        pyname_ret == Any.Int(4))\
or\
        Or(Any.is_Int(pyname_doit),
           And(Not(Any.b(pyname_doit) == true), Any.is_Bool(pyname_doit)),
           Any.is_String(pyname_doit))\
     and pyname_ret == Any.Int(5),
ret == pyname_ret)
""",
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


@pytest.mark.skip
def test_node_swap():
    # After an example in khurshid2003
    code = """
@dataclass
class Node:
    elem: int
    next: "Node"

def swapNode(node):
    if node.next is not None:
        next = node.next
        if node.elem - next.elem > 0:
            t = next
            node.next = t.next
            t.next = node
            return t
    return node
    """
    check_expression(
        code,
        [
            """
        (ite (Node.is_new pyname_node)
             (let ((pyname_next
    """
        ],
    )
