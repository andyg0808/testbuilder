#!/usr/bin/env python3
"""
generate_test_cases: Generates test cases for the return values of all functions in <source.py>

Usage: run.py [options] <source.py>

Options:
    --unroll-depth=<depth>  The depth to which to unroll loops
    --lines=<line,line,line>  Lines to generate tests for
    --verbose=<level>  Output all logging information for <level> and above
    --ignore=<file,file>  Ignore all logging from the specified files
    --no-color  Do not use color highlighting when printing Python
    --autopreprocess=<file.json>  Automatically run the preprocess
                                  rules in <file.json> on each input file.
    --autogen  Run the function under test with the suggested inputs to
               determine the expected output
"""

import json
from pathlib import Path

from docopt import docopt

import _z3config  # noqa: F401
import logconfig
import typeassert
from logbook import NullHandler
from testbuilder.generate import generate_tests
from testbuilder.requester import PlainRequester, Requester

typeassert.log.setLevel("ERROR")


def main(filename: str) -> None:
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

    test_cases = generate_tests(
        filepath,
        text,
        requester,
        depth=depth,
        lines=lines,
        changes=changes,
        autogen=autogen,
    )
    with open((filepath.parent / filepath.stem).as_posix() + "_test.py", "x") as tests:
        tests.write("from importlib import import_module")
        tests.write("\n\n".join(test_cases))


if __name__ == "__main__":
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

    main(opts["<source.py>"])
