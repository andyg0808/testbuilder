import ast
import os
import sys
from compiler import compiler
from contextlib import contextmanager
from importlib import import_module
from importlib.machinery import ModuleSpec
from importlib.util import module_from_spec
from pathlib import Path
from tempfile import NamedTemporaryFile, TemporaryDirectory

CODE = """
class Fish:
    def __init__(self):
        self.fish_count = 4
        self.fish_length = 46.8

    def total_length(self):
        return self.fish_count * self.fish_length
"""


def get_fish_module():
    spec = ModuleSpec("fish", None)
    expected = module_from_spec(spec)
    exec(CODE, expected.__dict__)
    return expected


def compare_fish_modules(left, right):
    left_fish = left.Fish()
    right_fish = right.Fish()

    assert left_fish.total_length() == right_fish.total_length()


def check_fish_module(actual):
    left = get_fish_module()
    compare_fish_modules(left, actual)


def test_code_compilation():
    """Test the basic case: can we load this module and will it deserialize
    correctly?"""
    tree = ast.parse(CODE)
    # TODO: Stop doing compile in compiler (and maybe rename it)
    module = compiler(tree)
    assert isinstance(module, str)

    spec = ModuleSpec("fish", None)
    loaded = module_from_spec(spec)
    exec(module, loaded.__dict__)

    check_fish_module(loaded)


def test_read_from_file():
    """
    If we create a file containing our module code, can we load it in the usual way?
    """
    with TemporaryDirectory() as tempdir:
        with NamedTemporaryFile(mode="w", suffix=".py", dir=tempdir) as fi:
            module = compiler(ast.parse(CODE))
            fi.write(module)
            fi.flush()
            path = Path(fi.name)
            sys.path.append(path.parent.as_posix())
            loaded = import_module(path.stem)
            sys.path.pop()
            check_fish_module(loaded)
