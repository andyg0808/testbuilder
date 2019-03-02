#!/usr/bin/env python3
"""
generate_test_cases: Generates test cases for the return values of all functions in <source.py>

Usage: run.py [--autogen|--golden=<file>] [options] <source.py>

Options:
    --unroll-depth=<depth>  The depth to which to unroll loops
    --lines=<line,line,line>  Lines to generate tests for
    --verbose=<level>  Output all logging information for <level> and above
    --ignore=<file,file>  Ignore all logging from the specified files
    --no-color  Do not use color highlighting when printing Python
    --autopreprocess=<file.json>  Automatically run the preprocess
                                  rules in <file.json> on each input file.
    --autogen  Run the function under test with the suggested inputs to
               determine the expected output.
    --basename=<name>  Filename for resulting tests. {parent} will be
                       replaced with the name of the parent directory
                       of the target file, {basename} will be replaced
                       with the full path and filename without the
                       extension, and {stem} will be replaced with the
                       filename alone without the extension.
    --golden=<file>  Equivalent to `--autogen`, except <file> will be
                     run instead of the function under test and its
                     result will be used as the expected output of the
                     function under test.
"""

import json
import signal
from pathlib import Path
from typing import Any, Mapping

import typeassert
from docopt import docopt
from logbook import NullHandler

import _z3config  # noqa: F401
import logconfig
from testbuilder.generate import generate_tests
from testbuilder.requester import PlainRequester, Requester


def signal_handler(num, f):
    breakpoint()
    return


signal.signal(signal.SIGUSR1, signal_handler)

typeassert.log.setLevel("ERROR")


def main(opts: Mapping[str, Any], filename: str) -> None:
    filepath = Path(filename)
    with filepath.open() as io:
        text = io.read()

    depth_s = opts["--unroll-depth"]
    if depth_s:
        depth = int(depth_s)
    else:
        depth = 10

    lines_s = opts["--lines"]
    if lines_s:
        lines = {int(s) for s in lines_s.split(",")}
    else:
        lines = None

    requester = None
    if opts["--no-color"]:
        requester = PlainRequester()
    else:
        requester = Requester()

    if opts["--autopreprocess"]:
        with open(opts["--autopreprocess"]) as f:
            changes = json.load(f)
    else:
        changes = None

    autogen = opts["--autogen"]
    golden = opts["--golden"]
    if autogen:
        autogen = filepath
    elif golden:
        autogen = Path(golden)

    test_cases = generate_tests(
        filepath,
        text,
        requester,
        depth=depth,
        lines=lines,
        changes=changes,
        autogen=autogen,
    )
    if opts["--basename"]:
        filename = opts["--basename"].format(
            parent=filepath.parent.as_posix(),
            basename=(filepath.parent / filepath.stem).as_posix(),
            stem=filepath.stem,
        )
    else:
        filename = (filepath.parent / filepath.stem).as_posix() + "_test.py"
    if Path(filename).resolve().as_posix() == "/dev/null":
        # Special-case /dev/null to throw out output
        return
    with open(filename, "x") as tests:
        tests.write("from importlib import import_module\n")
        tests.write("from testbuilder.pair import Pair\n")
        tests.write("from testbuilder import renderer\n")
        tests.write("from fractions import Fraction\n")
        tests.write("import pytest\n")
        tests.write("\n\n".join(test_cases))


def launch():
    opts = docopt(__doc__)

    NullHandler().push_application()

    ignores_s = opts["--ignore"]
    if ignores_s:
        ignores = set(ignores_s.split(","))
    else:
        ignores = set()

    def ignore_filter(r, h):
        return r.channel not in ignores

    verbosity = opts["--verbose"]
    logconfig.configure_fancylog(verbosity)

    main(opts, opts["<source.py>"])
