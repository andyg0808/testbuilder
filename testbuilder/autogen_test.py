import sys
from pathlib import Path
from tempfile import NamedTemporaryFile, TemporaryDirectory
from unittest.mock import create_autospec

from . import requester
from .generate import generate_tests


def Requester():
    return create_autospec(requester.Requester)()


def test_autosolve():
    code = """
def id(x):
    return x
    """
    expected = {
        """
from importlib import import_module
from testbuilder.pair import Pair
id = import_module("id").id
def test_id():
    x = 0
    actual = id(x)
    expected = 0
    assert actual == expected
    """
    }

    requester = Requester()
    tests = generate_tests(
        source=Path("id.py"), text=code, requester=requester, autogen=True
    )
    requester.input.assert_not_called()
    assert set(tests) == expected


def test_autosolve_real_module():
    code = """
from math import sin
def example(val):
    return sin(val)
    """
    requester = Requester()
    with TemporaryDirectory() as d:
        with NamedTemporaryFile(suffix=".py", mode="w", dir=d) as fi:
            fi.write(code)
            fi.flush()
            tests = generate_tests(
                source=Path(fi.name), text=code, requester=requester, autogen=True
            )
            sys.path.append(d)
            for test in tests:
                exec(test)
            sys.path.pop()
    requester.input.assert_not_called()
