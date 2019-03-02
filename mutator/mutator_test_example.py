import ast
from io import StringIO

import astor
import pytest

from testmutator import KilledMutation, Mutator


def check_mutations(original, *expected, complete=False):
    tree = ast.parse(original)
    mutations = []
    logs = {}
    iterator = iter(Mutator(tree))
    while True:
        trace = StringIO()
        try:
            mutation = next(iterator)
        except StopIteration:
            break
        if isinstance(mutation, KilledMutation):
            continue
        source = astor.to_source(mutation).strip()
        logs[source] = trace.getvalue()
        mutations.append(source)
    failed = False
    sources = set(mutations)
    for mutation in expected:
        rebuild = astor.to_source(ast.parse(mutation)).strip()
        if rebuild in sources:
            sources.remove(rebuild)
        else:
            failed = True
    if failed:
        raise AssertionError("Missing at least one expected result")
    if complete:
        assert len(expected) == len(mutations)


def test_sdl_mutations():
    check_mutations(
        """
a = 1 + 2
a += 32
b = 24
c = a + b
a = c - 36
    """,
        """
a = 1 + 2
b = 24
c = a + b
a = c - 36
""",
        """
a = 1 + 2
a += 32
b = 24
c = a + b
""",
    )


def test_sdl_boolop_mutation():
    check_mutations("a and b", "a", "b", "True", "False")

    check_mutations("a or b", "a", "b", "True", "False")

    check_mutations("a or b or c", "a or b", "b or c", "a or c", "True", "False")


def test_if_mutations():
    """
    These examples are taken directly from deng2013
    """
    check_mutations(
        """
def testIf():
    if a < 5:
        t = t + b + c
        a += 1
    elif a > 20:
        t = t + a + c
        b += 1
        """,
        """
def testIf():
    if True:
        t = t + b + c
        a += 1
    elif a > 20:
        t = t + a + c
        b += 1
        """,
        """
def testIf():
    if a < 5:
        a += 1
    elif a > 20:
        t = t + a + c
        b += 1
        """,
        """
def testIf():
    if a < 5:
        t = t + b + c
    elif a > 20:
        t = t + a + c
        b += 1
        """,
        """
def testIf():
    if a < 5:
        t = t + b + c
        a += 1
        """,
        """
def testIf():
    if a < 5:
        t = t + b + c
        a += 1
    elif True:
        t = t + a + c
        b += 1
        """,
        """
def testIf():
    if a < 5:
        t = t + b + c
        a += 1
    elif a > 20:
        b += 1
        """,
        """
def testIf():
    if a < 5:
        t = t + b + c
        a += 1
    elif a > 20:
        t = t + a + c
        """,
    )


def test_while_mutations():
    """
    These examples are taken directly from deng2013
    """
    check_mutations(
        """
def testWhile():
    while a < 5:
        t = t + b + c
        a += 1
        """,
        """
def testWhile():
    while True:
        t = t + b + c
        a += 1
        """,
        """
def testWhile():
    while a < 5:
        a += 1
        """,
        """
def testWhile():
    while a < 5:
        t = t + b + c
        """,
        """
def testWhile():
    pass
        """,
    )


def test_for_mutaions():
    """
These examples are adapted from deng2013
    """
    check_mutations(
        """
def testFor():
    for i in range(q, t):
        a = a + b + c
        b = b + c
        """,
        """
def testFor():
    for i in count(q):
        a = a + b + c
        b = b + c
        """,
        """
def testFor():
    for i in repeat(q):
        a = a + b + c
        b = b + c
        """,
        """
def testFor():
    for i in range(q, t):
        b = b + c
        """,
        """
def testFor():
    for i in range(q, t):
        a = a + b + c
        """,
    )


def test_for_repeat_mutation():
    """This example is not from deng2013, but it seems in the spirit of
it while better adapted to how Python works

    """
    check_mutations(
        """
def testFor():
    for i in lst:
        print(i)
""",
        """
def testFor():
    for i in repeat(lst):
        print(i)
""",
    )


def test_try_catch_mutation():
    """
These examples are taken directly from deng2013
    """
    check_mutations(
        """
def testTry():
    try:
        inStr = input()
        indata = int(inStr)
    except IOError:
        print("Could not read input")
    except ValueError:
        print("Must be numeric")
        """,
        """
def testTry():
    try:
        indata = int(inStr)
    except IOError:
        print("Could not read input")
    except ValueError:
        print("Must be numeric")
        """,
        """
def testTry():
    try:
        inStr = input()
    except IOError:
        print("Could not read input")
    except ValueError:
        print("Must be numeric")
        """,
    )
