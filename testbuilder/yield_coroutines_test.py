import inspect
from functools import singledispatch
from typing import Any, Union
from .coroutines import result

import pytest

from dataclasses import dataclass


@dataclass
class Node:
    pass


@dataclass
class Value(Node):
    value: Any


@dataclass
class Chain(Node):
    parent: Node
    value: Any


@dataclass
class Thing(Node):
    left: Node
    right: Node
    join: Node
    value: Any


@singledispatch
def visit(thing, stop):
    raise RuntimeError("Unknown type")


@visit.register(Value)
def visit_value(thing, stop):
    yield
    if thing is stop:
        return None
    else:
        return Value(visit(thing.value))


@visit.register(Thing)
def visit_thing(thing, stop):
    if thing is stop:
        return (yield)
    left = visit(thing.left, thing.join)
    right = visit(thing.right, thing.join)
    parent = yield from visit(thing.join, stop)
    left = result(left, parent)
    right = result(right, parent)
    return Thing(left=left, right=right, join=parent, value=visit(thing.value))


@visit.register(Chain)
def visit_chain(thing, stop):
    if thing is stop:
        return (yield)
    parent = yield from visit(thing.parent, stop)
    return Chain(parent=parent, value=visit(thing.value))


@visit.register(int)
def visit_int(thing):
    return thing * 2


def test_simple_visit():
    v = Value(24)
    val = result(visit(v, None), Value(1111))
    assert val == Value(48)


def test_visit_chain():
    v = Chain(parent=Value(24), value=25)
    val = result(visit(v, None), Value(1111))
    assert val == Chain(parent=Value(48), value=50)


def test_visit_join():
    join = Chain(parent=Value(24), value=25)
    left = Chain(parent=join, value=26)
    right = Chain(parent=join, value=27)
    v = Thing(left=left, right=right, join=join, value=28)
    val = result(visit(v, None), Value(1111))
    assert val.value == 56
    assert val.left.parent is val.join


def test_complex_visit():
    join2 = Chain(parent=Value(36), value=24)
    join1 = Thing(
        left=Chain(parent=join2, value=32),
        right=Chain(parent=join2, value=33),
        join=join2,
        value=12,
    )
    t = Thing(
        left=Chain(parent=join1, value=22),
        right=Chain(parent=join1, value=233),
        join=join1,
        value=93,
    )
    visit(t, None)
    gen = visit(t, None)
    val = result(gen, Value(1111))
    assert val.left.parent.join is val.right.parent.join
