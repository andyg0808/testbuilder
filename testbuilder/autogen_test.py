import sys
from pathlib import Path
from tempfile import NamedTemporaryFile, TemporaryDirectory
from unittest.mock import create_autospec

import pytest

from . import requester
from .generate import generate_tests


def Requester():
    return create_autospec(requester.Requester)()


BOILERPLATE = """
from importlib import import_module
from testbuilder.pair import Pair
from testbuilder import renderer
from fractions import Fraction
import pytest
"""


def test_autosolve():
    code = """
def id(x):
    return x
    """
    expected = {
        """
id = import_module("id").id
def test_id():
    x = 0
    actual = id(x)
    expected = 0
    assert renderer.convert_result(actual) == expected
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
            filepath = Path(fi.name)
            tests = generate_tests(
                source=filepath, text=code, requester=requester, autogen=filepath
            )
            sys.path.append(d)
            assert len(tests) == 1
            runline = f"\ntest_example()"
            test = tests[0]
            glos = {}
            exec(BOILERPLATE + test + runline, glos, glos)
            sys.path.pop()
    requester.input.assert_not_called()


def test_autosolve_with_golden_module():
    good_code = """
from math import sin
def example(val):
    return sin(val)
"""
    bad_code = """
from math import cos
def example(val):
    return cos(val)
"""
    requester = Requester()
    with TemporaryDirectory() as d:
        with NamedTemporaryFile(suffix=".py", mode="w", dir=d) as good_fi:
            good_fi.write(good_code)
            good_fi.flush()
            with NamedTemporaryFile(suffix=".py", mode="w", dir=d) as bad_fi:
                bad_fi.write(bad_code)
                bad_fi.flush()
                tests = generate_tests(
                    source=Path(bad_fi.name),
                    text=bad_code,
                    requester=requester,
                    autogen=Path(good_fi.name),
                )
                sys.path.append(d)
                assert len(tests) == 1
                runline = f"\ntest_example()"
                glos = {}
                with pytest.raises(AssertionError):
                    exec(BOILERPLATE + tests[0] + runline, glos, glos)
                sys.path.pop()
    requester.input.assert_not_called()
