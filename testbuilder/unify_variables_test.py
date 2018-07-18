import z3

from .converter import get_variable
from .expression_builder import unify_all_variables
from .variable_expander import expand_variables


def _unify_variables(left, right):
    """
    This is an older implementation of unify variables which should be clearer
    than the new one, since it is less complicated.
    """
    keys = left.keys() | right.keys()
    left_renaming = []
    right_renaming = []
    variables = {}
    for key in sorted(keys):
        if key in left and key in right and left[key] == right[key]:
            # If both sides have the same value for a key, don't increment the
            # variable number.
            variables[key] = left[key]
        else:
            max_val = max(left.get(key, 0), right.get(key, 0))
            next_name = get_variable(key, max_val)
            dest = z3.Int(next_name)
            if key in left and left[key] != max_val:
                name = get_variable(key, left[key])
                source = z3.Int(name)
                left_renaming.append(dest == source)
            if key in right and right[key] != max_val:
                name = get_variable(key, right[key])
                source = z3.Int(name)
                right_renaming.append(dest == source)
            variables[key] = max_val

    return variables, left_renaming, right_renaming


def compare_unification(left, right):
    old_unify_variables, left_edits, right_edits = _unify_variables(left, right)
    new_unify_variables, edit_list = unify_all_variables([left, right])
    assert old_unify_variables == new_unify_variables
    assert edit_list == [left_edits, right_edits]


def test_unify_all_variables():
    assert unify_all_variables([]) == ({}, [])
    compare_unification({"a": 1}, {"a": 1})
    compare_unification({"a": 1}, {"a": 2})
    compare_unification({"a": 6}, {"a": 2})


def test_multiple_unification():
    variable_lists = [
        {"a": 1, "b": 5, "c": 2},
        {"a": 1, "b": 6, "c": 2},
        {"a": 1, "b": 7, "c": 3},
    ]

    expected = (
        {"a": 1, "b": 7, "c": 3},
        [
            ["pyname_b_7 == pyname_b_5", "pyname_c_3 == pyname_c_2"],
            ["pyname_b_7 == pyname_b_6", "pyname_c_3 == pyname_c_2"],
            [],
        ],
    )

    results = unify_all_variables(variable_lists)
    assert expected[0] == results[0]
    assert len(expected[1]) == len(results[1])
    for expect, result in zip(expected[1], results[1]):
        assert len(expect) == len(result)
        #        for ce, cr in zip(expect, result):
        #            expanded = expand_variables(ce)
        #            assert z3.eq(expanded, cr)

        result_expr_mapping = {repr(e): e for e in result}
        for e in expect:
            r = result_expr_mapping[e]
            expanded = expand_variables(e)
            assert z3.eq(expanded, r)
