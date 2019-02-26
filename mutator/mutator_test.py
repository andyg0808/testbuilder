import ast
from io import StringIO

import astor
import pytest
from logbook import Logger

import hunter
from hunter import Q
from mutator import Mutator

log = Logger("mutator_test")


def check_mutations(original, *expected, complete=False):
    tree = ast.parse(original)
    mutations = []
    logs = {}
    iterator = iter(Mutator(tree))
    while True:
        trace = StringIO()
        hunter_action = hunter.CallPrinter(stream=trace)
        hunter.trace(module="mutator", action=hunter_action)
        try:
            mutation = next(iterator)
        except StopIteration:
            break
        finally:
            hunter.stop()
        source = astor.to_source(mutation).strip()
        logs[source] = trace.getvalue()
        mutations.append(source)
    print("Testing:")
    failed = False
    sources = set(mutations)
    for mutation in expected:
        rebuild = astor.to_source(ast.parse(mutation)).strip()
        if rebuild in sources:
            print("[32m✓ ", end="")
            sources.remove(rebuild)
        else:
            failed = True
            print("[31m✗ ", end="")
        print("-----⇩[0m\n" + rebuild)
    if sources:
        print("Extra mutations:\n------")
        for source in sources:
            print("------")
            print(source)
            log.debug(logs[source])
    if failed:
        raise AssertionError("Missing at least one expected result")
    if complete:
        assert len(expected) == len(mutations)


# def test_cmpop_mutations():
#     check_mutations("a < b", "a == b", "a > b")
#     check_mutations("a != b", "a == b", "a < b")


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
    check_mutations("a and b", "a", "b", "True", "False", "", complete=True)

    check_mutations("a or b", "a", "b", "True", "False", "", complete=True)

    check_mutations(
        "a or b or c", "a or b", "b or c", "a or c", "True", "False", "", complete=True
    )


def test_if_mutations():
    check_mutations(
        """
if a:
    4
else:
    5
        """,
        """
if True:
    4
else:
    5
        """,
        """
if False:
    4
else:
    5
        """,
        """
if a:
    pass
else:
    5
        """,
        """
if a:
    4
        """,
    )


def test_while_mutations():
    """
These examples are taken directly from
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
