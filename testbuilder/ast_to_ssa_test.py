import ast

from .ast_to_ssa import ast_to_ssa, last_line


def check_bounds(src):
    src = src.strip()
    tree = ast.parse(src)
    ssa = ast_to_ssa(depth=1, variables={}, node=tree)
    assert len(ssa.classes) == 1
    cls = next(iter(ssa.classes.values()))
    assert cls.first_line == 1
    assert cls.last_line == len(src.splitlines())


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
