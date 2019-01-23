import pytest

from .check_expression import ExpressionChecker

check_expression = ExpressionChecker(lambda b: b.wrappers().references().structures())


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
    Any.is_Int(Ref.Pair_left(store[Any.r(pyname_x)])),
        Any.is_Reference(pyname_x))
        """,
    )


def test_write_inferred_pair():
    """
    Test that writing a
    variable.
    """
    check_expression(
        "x.left = 0",
        """
And(Any.is_Reference(pyname_x),
    store_1 == Store(store, Any.r(pyname_x),
                     Ref.Pair(Any.Int(0), Ref.Pair_right(store[Any.r(pyname_x)]))),
)
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
pyname_x == Any.Reference(Reference(0)) \
and store_1 == Store(store, Reference(0), Ref.Pair(pyname_e, pyname_f))
    """,
    )


def test_ints_into_pair():
    check_expression(
        "x = Pair(1, 2)",
        """
pyname_x == Any.Reference(Reference(0)) \
and store_1 == Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(2)))
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
and Not(Any.i(Ref.Pair_left(store_2[Any.r(pyname_b)])) != 2)\
and Any.is_Int(Ref.Pair_left(store_2[Any.r(pyname_b)]))
        """,
    )


def test_right_field():
    check_expression(
        """
a.right = 3
a.right < 23
        """,
        """
Any.is_Reference(pyname_a) \
and store_1 == Store(store, Any.r(pyname_a), Ref.Pair(Ref.Pair_left(store[Any.r(pyname_a)]), Any.Int(3))) \
and Any.i(Ref.Pair_right(store_1[Any.r(pyname_a)])) < 23 \
and Any.is_Int(Ref.Pair_right(store_1[Any.r(pyname_a)])) \
and Any.is_Reference(pyname_a)
        """,
    )


def test_left_field():
    check_expression(
        """
a.left = 3
a.left < 23
        """,
        """
Any.is_Reference(pyname_a) \
and store_1 == Store(store, Any.r(pyname_a), Ref.Pair(Any.Int(3), Ref.Pair_right(store[Any.r(pyname_a)]))) \
and Any.i(Ref.Pair_left(store_1[Any.r(pyname_a)])) < 23\
and Any.is_Int(Ref.Pair_left(store_1[Any.r(pyname_a)]))\
and Any.is_Reference(pyname_a)
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


def test_infer_modify_pair():
    check_expression(
        """
def test(a):
    a.left = a.left + 32
    return a
    """,
        """
And(Any.is_Int(Ref.Pair_left(store[Any.r(pyname_a)])),
    Any.is_Reference(pyname_a),
    store_1 == Store(store, Any.r(pyname_a),
                     Ref.Pair(Any.Int(Any.i(Ref.Pair_left(store[Any.r(pyname_a)])) + 32),\
                              Ref.Pair_right(store[Any.r(pyname_a)]))),
    ret == pyname_a
)
""",
    )


def test_pair_with_odd_names():
    with pytest.raises(RuntimeError):
        check_expression(
            """
def test(a):
    a.first = 42
    return a
        """,
            None,
        )


def test_pair_equality():
    check_expression(
        """
a = Pair(1,1)
b = Pair(1,1)
a == b
""",
        """
pyname_a == Any.Reference(Reference(0)) and \
store_1 == Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(1))) and \
pyname_b == Any.Reference(Reference(1)) and \
store_2 == Store(store_1, Reference(1), Ref.Pair(Any.Int(1), Any.Int(1))) and \
Ref.Pair_left(store_2[Any.r(pyname_a)]) == Ref.Pair_left(store_2[Any.r(pyname_b)]) \
and Ref.Pair_right(store_2[Any.r(pyname_a)]) == Ref.Pair_right(store_2[Any.r(pyname_b)])
""",
    )


def test_pair_inequality():
    check_expression(
        """
a = Pair(1,1)
b = Pair(1,1)
a != b
""",
        """
pyname_a == Any.Reference(Reference(0)) and \
store_1 == Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(1))) and \
pyname_b == Any.Reference(Reference(1)) and \
store_2 == Store(store_1, Reference(1), Ref.Pair(Any.Int(1), Any.Int(1))) and \
Or(Ref.Pair_left(store_2[Any.r(pyname_a)]) != Ref.Pair_left(store_2[Any.r(pyname_b)]),
   Ref.Pair_right(store_2[Any.r(pyname_a)]) != Ref.Pair_right(store_2[Any.r(pyname_b)]))
""",
    )


def test_pair_identity():
    check_expression(
        "Pair(1,1) is not Pair(1,1)",
        """
Reference(0) != Reference(1) \
and store_2 == Store(Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(1))),
                         Reference(1), Ref.Pair(Any.Int(1), Any.Int(1)))
""",
    )
    check_expression(
        """
a = Pair(1,1)
a is a
""",
        """
pyname_a == Any.Reference(Reference(0)) \
and store_1 == Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(1))) \
and Any.r(pyname_a) == Any.r(pyname_a)
""",
    )
    check_expression(
        "Pair(1,1) is Pair(1,1)",
        """
Reference(0) == Reference(1) \
and store_2 == Store(Store(store, Reference(0), Ref.Pair(Any.Int(1), Any.Int(1))),
                     Reference(1), Ref.Pair(Any.Int(1), Any.Int(1)))
""",
    )
