import pytest

from .check_expression import ExpressionChecker

check_expression = ExpressionChecker(
    lambda b: b.references().structures().wrappers().none()
)


@pytest.mark.xfail(reason="Need to figure out what it should make")
def test_function_call_with_attribute():
    check_expression(
        """
def called(a):
    return a.left
def caller(b):
    return called(b)
        """,
        "ret == Ref.Pair_left(store[Any.r(pyname_b)])",
        simplify=True,
    )


def test_recursive_call_with_conditional_and_attributes():
    check_expression(
        """
def func(a, b):
    if b*1 == 0:
        return a.left
    else:
        return func(a.right, b)
""",
        """
And(
    Not(0 == Any.i(pyname_b)*1),
    Any.is_Int(pyname_b),
    function_func_1_pyname_a == Ref.Pair_right(store[Any.r(pyname_a)]),
    function_func_1_pyname_b == pyname_b,
    0 == Any.i(function_func_1_pyname_b) * 1,
    function_func_1_return == Ref.Pair_left(store[Any.r(function_func_1_pyname_a)]),
    ret == function_func_1_return
)
""",
    )


def test_recursive_call():
    check_expression(
        """
def func(a):
    if a > 1:
        return a
    else:
        return func(a)
        """,
        """
And(
    Not(1 < Any.i(pyname_a)),
    Any.is_Int(pyname_a),
    function_func_1_pyname_a == pyname_a,
    1 < Any.i(function_func_1_pyname_a),
    function_func_1_return == function_func_1_pyname_a,
    ret == function_func_1_return
)
""",
    )


def test_function_call():
    check_expression(
        """
def double(i):
    return i * 2

def call_func(i):
    return double(i)
        """,
        # "ret == 2 * pyname_i",
        """
        And(function_double_1_pyname_i == pyname_i,
        function_double_1_return == Any.Int(Any.i(function_double_1_pyname_i) * 2),
            Any.is_Int(function_double_1_pyname_i),
        ret == function_double_1_return)
        """,
    )


@pytest.mark.xfail
def test_deep_call():
    check_expression(
        """
def bottom(i):
    return i * 2

def middle(i):
    p = bottom(i) + 2
    return p

def top(i):
    q = middle(i)
    q += 23
    return q * 23
        """,
        """
        And(function_middle_1_pyname_i == pyname_i,
        function_bottom_1_pyname_i == function_middle_1_pyname_i,
        function_bottom_1_return == function_bottom_1_pyname_i * 2,
        function_middle_1_pyname_p == function_bottom_1_return + 2,
        function_middle_1_return == function_middle_1_pyname_p,
        pyname_q == function_middle_1_return,
        pyname_q_1 == pyname_q + 23
        ret == pyname_q_1 * 23)
""",
    )


def test_conditional_functions():
    # TODO: Extract the initial line of each of the innermost `And`s
    # into the outer `And`.
    check_expression(
        """
def conditioned(i):
    if i > 4:
        return 6
    else:
        return 14

def run_func(i):
    return i * conditioned(i)
        """,
        """
        And(
        Or(And(function_conditioned_1_pyname_i == pyname_i,
               Any.i(function_conditioned_1_pyname_i) > 4,
               Any.is_Int(function_conditioned_1_pyname_i),
               function_conditioned_1_return == Any.Int(6)),
           And(function_conditioned_1_pyname_i == pyname_i,
               Not(Any.i(function_conditioned_1_pyname_i) > 4),
               Any.is_Int(function_conditioned_1_pyname_i),
               function_conditioned_1_return == Any.Int(14))),
        ret == Any.Int(Any.i(pyname_i) * Any.i(function_conditioned_1_return)),
        Any.is_Int(pyname_i))
        """,
    )


def test_simplest_function_call():
    check_expression(
        """
def inner(i):
    return i
def outer(i):
    return inner(i)
        """,
        """
        And(function_inner_1_pyname_i == pyname_i,
        function_inner_1_return == function_inner_1_pyname_i,
        ret == function_inner_1_return)
        """,
    )


@pytest.mark.skip
def test_function_recursion():
    check_expression(
        """
def zero(i):
    if i == 0:
        return 0
    else:
        return zero(i-1)
        """,
        "ret == 0",
    )


def test_multiple_functions():
    check_expression(
        """
def first_func(a):
    return a * 5

def second_func(b):
    return b + 8
        """,
        "ret == Any.Int(Any.i(pyname_b) + 8) and Any.is_Int(pyname_b)",
    )


def test_default_arguments():
    check_expression(
        """
def defaulted(a, b=1):
    return a + b

def caller(a):
    return defaulted(a)
        """,
        """
And(
        function_defaulted_1_pyname_a == pyname_a,
        function_defaulted_1_pyname_b == Any.Int(1),
        function_defaulted_1_return == Any.Int(Any.i(function_defaulted_1_pyname_a) + Any.i(function_defaulted_1_pyname_b)),
        Any.is_Int(function_defaulted_1_pyname_a),
        ret == function_defaulted_1_return)
""",
    )
