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
"""

from pathlib import Path

from docopt import docopt
from logbook import NullHandler, StderrHandler

import typeassert
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

    test_cases = generate_tests(filepath, text, requester, depth=depth, lines=lines)
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
    if verbosity:
        StderrHandler(level=verbosity, filter=ignore_filter).push_application()
    else:
        StderrHandler(level="NOTICE", filter=ignore_filter).push_application()

    main(opts["<source.py>"])
