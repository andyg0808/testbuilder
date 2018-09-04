import re
from typing import List

import logbook
import pytest
from hypothesis import given
from hypothesis.strategies import builds, deferred, integers, lists, one_of, recursive

from dataclasses import dataclass

from .visitor import GatherVisitor, SimpleVisitor, UpdateVisitor, VisitError


class Node:
    pass


@dataclass
class Leaf(Node):
    value: int


@dataclass
class Parent(Node):
    left: Node
    right: Node
    links: List[Node]


node = deferred(lambda: one_of(leaf, parent))
leaf = builds(Leaf, value=integers())
parent = recursive(
    leaf, lambda node: builds(Parent, left=node, right=node, links=lists(node))
)
# parent = builds(Parent, left=node, right=node, links=lists(node))
node = one_of(leaf, parent)


def gather_from_tree(tree):
    if isinstance(tree, Leaf):
        return [tree.value]
    else:
        links = []
        for link in tree.links:
            links += gather_from_tree(link)
        return gather_from_tree(tree.left) + gather_from_tree(tree.right) + links


@given(node)
def test_gather_visitor(tree):
    class Gatherer(GatherVisitor[int]):
        def visit_Leaf(self, node: Leaf) -> List[int]:
            return [node.value]

    expected = gather_from_tree(tree)
    assert Gatherer()(tree) == expected


def check_tree_equal(left, right):
    assert type(left) is type(right)
    if isinstance(left, Leaf):
        assert 2 * left.value == right.value
    else:
        check_tree_equal(left.left, right.left)
        check_tree_equal(left.right, right.right)
        assert len(left.links) == len(right.links)
        for l, r in zip(left.links, right.links):
            check_tree_equal(l, r)


@given(node)
def test_gather_visitor(tree):
    class Updater(UpdateVisitor):
        def visit_Int(self, node: int) -> int:
            return 2 * node

    check_tree_equal(tree, Updater()(tree))


@given(integers())
def test_suggestion(i):
    class Simple(SimpleVisitor):
        def visit_int(self, i: int):
            return i

    with pytest.raises(VisitError, match=r"visit_int"):
        Simple()(i)


@given(integers())
def test_oddity_warning(i):
    class Simple(SimpleVisitor):
        def visit_Int(self, i: int):
            return i

        def visit_thing(thing: list):
            return thing

    with logbook.TestHandler() as handler:
        expected = re.compile("visit_thing .* too few parameters")
        Simple()(i)
        assert handler.has_warning(expected)
