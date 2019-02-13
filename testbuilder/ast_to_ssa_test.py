import ast

from . import nodetree as n
from .ast_to_ssa import ast_to_ssa


def check_bounds(src):
    src = src.strip()
    tree = ast.parse(src)
    ssa = ast_to_ssa(depth=1, variables={}, node=tree)
    assert len(ssa.classes) == 1
    cls = next(iter(ssa.classes.values()))
    assert cls.first_line == 1
    assert cls.last_line == len(src.splitlines())


def check_parse(src, expected):
    src = src.strip()
    tree = ast.parse(src)
    ssa = ast_to_ssa(depth=1, variables={}, node=tree)
    contents = ssa.code.end.parents[0].code[0]
    assert contents == expected


def test_basic_class_bounds():
    check_bounds(
        """
class Fishes(Animals):
    def __init__(self):
        self.fins = 7
        self.tails = 1
        """
    )


def test_pass_class_bounds():
    check_bounds(
        """
class Fishes(Animals):
    pass
        """
    )


def test_pass_function_class_bounds():
    check_bounds(
        """
class Fishes(Animals):
    def __init__(self):
        pass
        """
    )


def test_code_class_bounds():
    check_bounds(
        """
@dataclass
class Fishes:
    fins: int
    tails: int
"""
    )


def test_code_ending_class_bounds():
    check_bounds(
        """
class Fishes:
    def thing(self):
        pass
    fishes = 0
"""
    )


def test_multi_split_funcs():
    check_bounds(
        """
class Fishes:
    def __init__(self):
        self.fins = 7
        self.tails = 1

    skeleton = True

    def complete(self):
        return (self.fins == 7) and (self.tails == 1)

    brain = True
"""
    )


def test_tuples():
    check_parse(
        "(1,2,a)",
        n.Expr(line=1, value=n.TupleVal([n.Int(1), n.Int(2), n.Name("a", 0)])),
    )
