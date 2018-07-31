import ast
import sys
from pprint import pprint
from typing import Mapping, Optional, Sequence, Set, Union

import pytest
from logbook import StreamHandler, debug, warn

from . import basic_block
from .basic_block import BasicBlock
from .build_tree import RETURNBLOCK, TreeBuilder, TreeWalker, build_tree
from .slicing import Conditional, take_slice
from .test_utils import write_dot

StreamHandler(sys.stdout).push_application()


Example = Union[int, Set[int]]
ExampleMap = Mapping[int, Example]


class Required:
    def __init__(self, value):
        self.value = value


class NotRequired:
    def __init__(self, value):
        self.value = value


def check_type(l, t):
    for i, v in enumerate(l):
        assert v is None or isinstance(
            v, t
        ), "Expected {} at index {} to be a {}".format(v, i, t)


def check_tree(expected: Sequence[Optional[str]], tree: BasicBlock):
    check_block_tree(expected, tree)


def check_block_tree(expectations, tree, stop=None):
    """
    Check that `tree` of basic blocks matches the description provided in
    `expectations`
    
    Args:
        expectations: A list of expectations which should be fulfilled by the block tree in `tree`
        tree: The root of a basic block tree which will be compared to the expectations
        stop: A block which, if found, should be treated as not existing. Used
              to avoid searching through loops repeatedly.
    """

    # This allows us to avoid getting caught in loops. We break out when we
    # reach the point where we started.
    if tree is stop:
        # There should be no more items in the expectations, or we didn't have
        # enough code before coming to the stop block.
        assert not expectations
        debug("Stopping on block {}", tree.number)

        return

    debug("Checking block {}", tree.number)

    check_required_block(expectations, tree, stop)


def skip_empty_blocks(expectations, tree, stop):
    if empty_block(tree) and len(tree.children) == 1:
        debug("Skipping empty block {}", tree.number)
        # Forward tree to next block, if this one is completely empty.
        skip_empty_blocks(expectations, tree.children[0], stop)
    else:
        check_block_tree(expectations, tree, stop)


def check_required_block(expectations, tree, stop):
    # We don't want the expectations just petering out. To officially
    # extinguish them, either the last block must end with just enough code to
    # use all of them, or the last block must be empty and the last expectation
    # must be a None.
    assert expectations, "Insufficient expectations"

    debug("Checking required block {}", tree.number)

    expected = expectations[0]

    if expected is None:
        check_none(expectations, tree, stop)
    elif (
        isinstance(expected, str)
        or isinstance(expected, Required)
        or isinstance(expected, NotRequired)
    ):
        check_code_block(expectations, tree, stop)
    elif isinstance(expected, tuple):
        if len(expected) == 2:
            check_loop(expectations, tree, stop)
        elif len(expected) == 3:
            check_conditional(expectations, tree, stop)
        else:
            raise AssertionError(
                "Invalid tuple length: {} has length {} which is not 2 or 3".format(
                    expected, len(expected)
                )
            )


def check_loop(expectations, tree, stop):
    print("checkloop expecting", expectations, "block", tree.number)
    expected = expectations[0]
    # Check basic properties we expect of loop expectations
    assert len(expected) == 2
    expected_cond, expected_body = expected
    assert isinstance(expected_cond, str)
    assert isinstance(expected_body, list)

    # Check basic properties we expect of loop blocks
    assert tree.type == basic_block.Loop
    assert len(tree.children) == 2
    assert len(tree.parents) == 2
    assert tree.conditional
    assert is_descendent(tree.children[0], tree.parents[0])

    # Check that we have the right conditional
    check_code(expected_cond, tree.conditional.code)
    check_block_tree(expected_body, tree.children[0], tree)

    check_block_tree(expectations[1:], tree.children[1], stop)


def check_conditional(expectations, tree, stop):
    expected = expectations[0]
    # Check basic properties of conditional expectations
    assert len(expected) == 3
    expected_cond, expected_true, expected_false = expected
    assert isinstance(expected_cond, str)
    assert isinstance(expected_true, list) or expected_true is None
    assert isinstance(expected_false, list) or expected_false is None

    # Check basic properties of conditional blocks
    assert tree.type == basic_block.StartConditional
    # The third child is the join block
    assert len(tree.children) == 3
    assert len(tree.parents) == 1
    true_branch, false_branch, join = tree.children
    assert tree.conditional
    assert join.type == basic_block.Conditional
    if join.number != RETURNBLOCK:
        assert len(join.children) == 1
        assert len(join.parents) == 3
        assert is_descendent(true_branch, join.parents[0])
        assert is_descendent(false_branch, join.parents[1])
        assert tree is join.parents[2]

    debug("Checking conditional block {}", tree.number)
    check_code(expected_cond, tree.conditional.code)

    check_conditional_fork(expected_true, true_branch, join)
    check_conditional_fork(expected_false, false_branch, join)

    check_block_tree(expectations[1:], join, stop)


def check_conditional_fork(expectations, tree, stop):
    """
    Check that a branch of a conditional matches the expectation provided.
    Allows expectations to be `None`, which causes it to check that all blocks
    in that branch of the tree are empty. This makes handling slices of one
    side of an `if` easier.
    """
    if expectations is None:
        check_empty_tree(tree, stop)
    else:
        check_block_tree(expectations, tree, stop)


def check_empty_tree(tree, stop):
    if tree is stop:
        debug("Found stop block {}.", tree.number)
        return

    assert empty_block(tree)

    debug("Block {} is empty as expected.", tree.number)

    # Search using standard pattern; run check_empty_tree on each block found
    if tree.type == basic_block.Loop:
        assert len(tree.children) == 2
        assert len(tree.parents) == 2
        check_empty_tree(tree.children[0], tree.children[2])
        check_empty_tree(tree.children[1], tree.children[2])
    elif tree.type == basic_block.StartConditional:
        assert len(tree.children) == 3
        assert len(tree.parents) == 1
        check_empty_tree(tree.children[0], tree)
        check_empty_tree(tree.children[1], stop)
    elif tree.type == basic_block.Code:
        if tree.number != RETURNBLOCK:
            assert len(tree.parents) == 1
        if tree.children:
            assert len(tree.children) == 1
            check_empty_tree(tree.children[0], stop)
    elif tree.type == basic_block.Conditional:
        if tree.number != RETURNBLOCK:
            assert len(tree.parents) == 3
        if tree.children:
            assert len(tree.children) == 1
            check_empty_tree(tree.children[0], stop)
    else:
        raise AssertionError("Invalid tree type: {}".format(tree.type))


def check_code_block(expectations, tree, stop):
    assert len(expectations) >= len(tree.code)

    for expected, statement in zip(expectations, tree.code):
        check_statement(expected, statement, tree)

    if len(expectations) == len(tree.code):
        # If we just used up the expectations, that's fine, but we want to make
        # sure we checked all the code.
        check_done(tree, stop)
    else:
        assert len(tree.children) == 1
        if tree.type == basic_block.Conditional:
            assert len(tree.parents) == 3
        check_block_tree(expectations[len(tree.code) :], tree.children[0], stop)


def check_statement(expected, statement, tree):
    if isinstance(expected, Required):
        assert tree.required
        expected = expected.value
    if isinstance(expected, NotRequired):
        assert not tree.required
        expected = expected.value
    assert isinstance(expected, str)
    check_code(expected, statement.code)


def check_code(expected: str, actual: ast.AST):
    expected_dump = ast.dump(ast.parse(expected).body[0])
    actual_dump = ast.dump(actual)
    assert expected_dump == actual_dump


def check_none(expectations, tree, stop):
    # Things we expect of a none expectation
    assert expectations[0] is None

    # Things we expect of a block on which a None has been asserted
    assert empty_block(tree)

    if tree.children:
        assert len(tree.children) == 1
        # check_block_tree(expectations[1:], tree.children[0], stop)
        debug("{} was empty as expected. Checking child block...", tree.number)
        # skip_empty_blocks(expectations[1:], tree.children[0], stop)
        check_block_tree(expectations[1:], tree.children[0], stop)
    else:
        debug("{} was empty as expected and has no children.", tree.number)
        # This must be the last item in the list of expectations
        assert len(expectations) == 1


def check_done(tree, stop):
    """
    Checks that tree has no children, or that the only child tree has is the
    one we're supposed to ignore.
    """
    if len(tree.children) == 1:
        assert tree.children[0] == stop
    else:
        assert len(tree.children) == 0


def is_descendent(node, maybeDescendent, seen=None) -> bool:
    if not seen:
        seen = set()

    if node in seen:
        return False
    else:
        seen.add(node)

    if node is maybeDescendent:
        return True
    for child in node.children:
        if is_descendent(child, maybeDescendent, seen):
            return True
    return False


def empty_block(tree):
    return not tree.conditional and not tree.code


def test_check_empty_tree():
    # Check with chained empty basic blocks:
    tree = BasicBlock(1).start_parent().start_parent()
    expected = [None]
    with pytest.raises(AssertionError):
        check_tree(expected, tree)
    with pytest.raises(AssertionError):
        check_tree(expected * 2, tree)
    check_tree(expected * 3, tree)
    with pytest.raises(AssertionError):
        check_tree(expected * 4, tree)


def create_tree(code: str, write_tree: str = "", line=-1):
    parsed = ast.parse(code.strip())
    tree = build_tree(parsed)
    if write_tree != "":
        print("writing tree!")
        write_dot(tree.dot(), write_tree)
        write_dot(tree.build_tree()[0].dot(), write_tree)
    print("done writing")
    s = take_slice(parsed, line)
    if not s:
        warn("No such slice exists")
        return None
    print("before", s.walk_tree())
    return tree.inflate(s)


def check_tree_builder(expected: str, code: str, write_tree: str = "", line=-1):
    tree = create_tree(code, write_tree, line=line)
    if write_tree != "":
        write_dot(tree.dot(), write_tree)
    check_tree(expected, tree.entrance)


def test_tree_building():
    tree = {1: [3], 2: [3], 3: [4, 5]}
    bt = TreeBuilder(mapping={}, tree=tree, types={}, returns={}, node_order={})
    block_tree = bt.build_tree()
    assert block_tree[1].children == [block_tree[3]]
    assert block_tree[2].children == [block_tree[3]]
    assert block_tree[3].children == [block_tree[4], block_tree[5]]
    for i in range(1, 6):
        assert isinstance(block_tree[i], BasicBlock)


def test_tree_building2():
    tree = {
        0: [],
        1: [2],
        2: [3, 8],
        3: [4],
        4: [5, 7, 6],
        5: [6],
        6: [2],
        7: [6],
        8: [0],
    }
    types = {
        2: basic_block.Loop,
        4: basic_block.StartConditional,
        6: basic_block.Conditional,
    }
    node_order = {2: [6, 1], 6: [5, 7, 4]}
    bt = TreeBuilder(
        mapping={}, tree=tree, types=types, returns={}, node_order=node_order
    )
    block_tree = bt.build_tree()
    assert block_tree[0].children == []
    assert block_tree[1].children == [block_tree[2]]
    assert block_tree[2].children == [block_tree[3], block_tree[8]]
    assert block_tree[3].children == [block_tree[4]]
    assert block_tree[4].children == [block_tree[5], block_tree[7], block_tree[6]]
    assert block_tree[5].children == [block_tree[6]]
    assert block_tree[6].children == [block_tree[2]]
    assert block_tree[7].children == [block_tree[6]]
    assert block_tree[8].children == [block_tree[0]]

    assert block_tree[0].parents == [block_tree[8]]
    assert block_tree[1].parents == []
    assert block_tree[2].parents == [block_tree[6], block_tree[1]]
    assert block_tree[3].parents == [block_tree[2]]
    assert block_tree[4].parents == [block_tree[3]]
    assert block_tree[5].parents == [block_tree[4]]
    assert block_tree[6].parents == [block_tree[5], block_tree[7], block_tree[4]]
    assert block_tree[7].parents == [block_tree[4]]
    assert block_tree[8].parents == [block_tree[2]]


def test_tree_spec_creation():
    code = """
if ...:
    while ...:
        pass
else:
    while ...:
        if ...:
            pass
        else:
            pass
    if ...:
        pass
"""

    from .test_utils import show_dot

    tw = TreeWalker()
    tw.visit(ast.parse(code))
    builder = tw.get_builder()
    tree = builder.build_tree()
    # show_dot(tree[1].dot())
    assert tw.tree == {
        0: [],
        1: [2],
        2: [3, 8, 7],
        3: [4],
        4: [5, 6],
        5: [4],
        6: [7],
        7: [22],
        8: [9],
        9: [10, 16],
        10: [11],
        11: [12, 14, 13],
        12: [13],
        13: [15],
        14: [13],
        15: [9],
        16: [17],
        17: [18, 20, 19],
        18: [19],
        19: [21],
        20: [19],
        21: [7],
        22: [],
    }

    assert tw.node_order == {
        4: [5, 3],
        7: [6, 21, 2],
        9: [15, 8],
        13: [12, 14, 11],
        19: [18, 20, 17],
    }


def test_block_creation():
    code = """
def example(a):
    return a
    """
    expected = [Required("return a"), None]
    check_tree_builder(expected, code)


def test_linear_tree():
    code = """
def example(a, b):
    a = 3
    b = a
    return b
    """
    expected = ["a = 3", "b = a", Required("return b"), None]
    check_tree_builder(expected, code)


def test_tree_linearization():
    code = """
def example(a, b):
    a = b
    b = 3
    return a + b
    """
    expected = ["a = b", "b = 3", Required("return a + b"), None]
    check_tree_builder(expected, code)


def test_if_linearization():
    code = """
def example(a, b):
    if a < b:
        r = a
    return r
    """
    expected = [
        None,
        ("a < b", [NotRequired("r = a")], None),
        Required("return r"),
        None,
    ]
    check_tree_builder(expected, code)


def test_returning_from_if():
    code = """
def things(a, b):
    if 4 < 3:
        return a
    else:
        return b
    """
    expected = [None, ("4 < 3", None, ["return b"]), None]
    check_tree_builder(expected, code)


def test_if_else_linearization():
    code = """
def example(a, b):
    if a < b:
        r = a
    else:
        r = b
    return r
    """
    expected = [None, ("a < b", ["r = a"], ["r = b"]), "return r", None]
    check_tree_builder(expected, code)


def test_nested_ifs():
    code = """
def min(a, b, c):
    if a < b:
        if a < c:
            return a
        else:
            return c
    else:
        if b < c:
            return b
        else:
            return c
    """
    expected = [None, ("a < b", None, [None, ("b < c", None, ["return c"])]), None]
    check_tree_builder(expected, code)


def test_forked_mutation(request):
    code = """
def forked(a):
    c = 0
    if a < 3:
        c = c + 3
    else:
        c = c + 2
    return c
    """
    expected = ["c = 0", ("a < 3", ["c = c + 3"], ["c = c + 2"]), "return c", None]
    check_tree_builder(expected, code)


def test_while_loop():
    code = """
def while_away(i):
    while i > 0:
        i -= 1
    return i
    """
    expected = [None, ("i > 0", ["i -= 1"]), "return i", None]
    check_tree_builder(expected, code)


def test_while_construction():
    code = """
def while_away(i):
    while i > 0:
        i -= 1
    return i
    """
    tree = create_tree(code).entrance
    assert len(tree.children) == 1
    tree = tree.children[0]

    assert len(tree.children) == 2
    for child in tree.children:
        if type(child.conditional) == Conditional:
            assert child is tree
        else:
            assert child is not tree


def test_conditional_while():
    code = """
def maybe_while(a, b):
    if a < 4:
        while b > 0:
            b -= 1
    else:
        b = a
    return b
    """
    expected = [
        None,
        ("a < 4", [None, ("b > 0", ["b -= 1"]), None], ["b = a"]),
        "return b",
        None,
    ]
    check_tree_builder(expected, code)


def test_while_conditional():
    code = """
while a > 1:
    if b > 1:
        a -= b
    else:
        a += b
return a
    """
    expected = [
        None,
        ("a > 1", [None, ("b > 1", ["a -= b"], ["a += b"]), None, None]),
        "return a",
        None,
    ]
    check_tree_builder(expected, code)


def test_early_return():
    code = """
return 1
return 2
    """
    tree = create_tree(code, line=2)
    assert tree is None


def test_is_parent():
    b = TreeBuilder({}, {}, {}, {}, {})
    start = BasicBlock()
    end = start.start_block().start_block()
    end.children.append(start)
    start.parents.append(end)
    assert b._is_ancestor(start, end, set())
