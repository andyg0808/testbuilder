import ast

import astor
import pytest

from mutator import Mutator


def check_mutations(original, *expected, complete=False):
    tree = ast.parse(original)
    mutations = set(Mutator(tree))
    for m in mutations:
        print(ast.dump(m))
    sources = set()
    for mutation in mutations:
        sources.add(astor.to_source(mutation).strip())
    print("Mutated code:\n" + "\n\n".join(sources))
    for mutation in expected:
        rebuild = astor.to_source(ast.parse(mutation)).strip()
        assert rebuild in sources
    if complete:
        assert len(expected) == len(sources)


def test_cmpop_mutations():
    check_mutations("a < b", "a == b", "a > b")
    check_mutations("a != b", "a == b", "a < b")


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


def test_conditional_mutations():
    check_mutations(
        """
if a:
    return 4
else:
    return 5
        """,
        """
if True:
    return 4
else:
    return 5
        """,
        """
if False:
    return 4
else:
    return 5
        """,
        """
if a:
    pass
else:
    return 5
        """,
        """
if a:
    return 4
else:
    pass
        """,
    )
