import ast
from functools import partial

import pytest
from toolz import pipe

import z3

from .expression_builder import get_expression
from .type_builder import TypeBuilder
from .variable_expander import expand_variables
from .z3_types import Reference, diff_expression, print_diff


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
    builder.wrappers().references().structures()
    Registrar = builder.build()

    if isinstance(expected, str):
        store_sort = z3.ArraySort(Reference, Registrar.reftype)
        local_vals = {
            "store": z3.Const("store", store_sort),
            "store_1": z3.Const("store_1", store_sort),
            "store_2": z3.Const("store_2", store_sort),
            "Reference": lambda i: Reference.Reference(i),
        }
        expected = expand_variables(expected, Registrar, local_vals=local_vals)
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
        if diff is not None:
            print_diff(diff)
            raise AssertionError("Expressions differ")


@pytest.mark.skip(
    reason="Not planning to implement full support for custom classes for now"
)
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
        pyname_e == Ref.Pair(Any.Int(2), Any.Int(3))\
        and pyname_left == Ref.Pair_left(pyname_e)\
        and pyname_right == Ref.Pair_right(pyname_e)
""",
    )


# If I can name a store to fetch a variable from, couldn't I stringify
# the store access and treat it as the name of a variable in which the
# current value is stored?  If that's so, what's to keep me from
# tracking all the values currently in the store and using a separate
# variable for each version?

# Because the separate variables are awkward to access when dealing
# wth potential aliasing in input variables. I need to allow inputs to
# choose arbitrary reference values.

# Basically, the challenge is allowing aliasing in the initial values
# of parameters. We could make all values currently in the store
# available via Or assignment. But that's going to be messy. So
# keeping the store in the solver's domain and using integer values as
# keys allows us to simply create references to any item in the store:
# we choose an integer less than or equal to the largest index in the
# store.  Allocating new store items seems interesting, though. How do
# we figure out if an item should

# Very few constructs will be ambigous about whether they refer to a
# reference or not. Only references can have attribute
# accesses. Without an attribute access, it's not necessarilly as
# clear whether something is a reference, but there can't be any
# operations not defined for that reference.


def test_basic_pair():
    check_expression(
        "x = Pair(1,2)",
        """
        pyname_x == Any.Reference(Reference(0)) \
        and store_1 == Store(store, Reference(0),
                             Ref.Pair(Any.Int(1), Any.Int(2)))
        """,
        #         """
        # # pyname_x_store_1 = Ref.Pair(Any.Int(1), Any.Int(2))
        #         """,
    )


def test_read_inferred_pair():
    """
    Test the constructs around inferring a reference to a pair in a
    variable.
    """
    check_expression(
        "x.left > 0",
        """
And(Any.i(Ref.Pair_left(store[Any.r(pyname_x)])) > 0,
    And(Any.is_Reference(pyname_x),
        Any.is_Int(Ref.Pair_left(store[Any.r(pyname_x)]))))
        """,
    )


@pytest.mark.xfail
def test_write_inferred_pair():
    """
    Test that writing a
    variable.
    """
    check_expression(
        "x.left > 0",
        """
Any.i(Ref.Pair_left(store[Any.r(pyname_x)])) > 0
        """,
    )


def test_variable_into_pair():
    check_expression(
        """
e = 1
f = 2
x = Pair(e, f)
""",
        """
        And(
        pyname_e == Any.Int(1),
        pyname_f == Any.Int(2),
        pyname_x == Any.Reference(Reference(0)),
        store_1 == Store(store, Reference(0), Ref.Pair(pyname_e, pyname_f)),
        )
        """,
    )


@pytest.mark.xfail
def test_unconstrained_variables_into_pair():
    """
    Create a pair from two unconstrained variables. We want the pair
    to realize that the variables are both `Any`s, as are its slots,
    and just match the two, instead of expanding the variables and
    running a full Cartesian product on the possible subtypes
    """
    check_expression(
        "x = Pair(e, f)",
        """
store_1 == Store(store, 0, Ref.Pair(pyname_e, pyname_f)) \
and pyname_x == Any.Reference(Reference(0))
    """,
    )


@pytest.mark.xfail
def test_ints_into_pair():
    check_expression(
        "x = Pair(1, 2)",
        """
pyname_x == Ref.Pair(Any.Int(1), Any.Int(2))
""",
    )


def test_alias_pair():
    check_expression(
        """
a = Pair(1,2)
b = a
a.left = 2
not (b.left != 2)
        """,
        """
pyname_a == Any.Reference(Reference(0)) \
and store_1 == Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(2))) \
and pyname_b == pyname_a \
and store_2 == Store(store_1, Any.r(pyname_a),
          Ref.Pair(Any.Int(2), Ref.Pair_right(store_1[Any.r(pyname_a)]))) \
and Not(Ref.Pair_left(store_2[Any.r(pyname_b)]) != Any.Int(2))
        """,
    )


def test_read_pair():
    check_expression(
        """
a = Pair(1, 2)
x = a.left
        """,
        """
pyname_a == Any.Reference(Reference(0))\
and store_1 == Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(2)))\
and pyname_x == Ref.Pair_left(store_1[Any.r(pyname_a)])
        """,
    )


def test_modify_pair():
    check_expression(
        """
x = Pair(1,2)
x.left = 3
    """,
        """
pyname_x == Any.Reference(Reference(0))\
and store_1 == Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(2)))\
and store_2 == Store(store_1, Any.r(pyname_x), Ref.Pair(Any.Int(3), Ref.Pair_right(store_1[Any.r(pyname_x)])))
    """,
    )
