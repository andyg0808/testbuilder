#!/usr/bin/env python3
"""
generate_test_cases: Generates test cases for the return values of all functions in <source.py>

Usage: run.py [options] <source.py>

Options:
    --unroll-depth=<depth>  The depth to which to unroll loops
"""

import sys
from pathlib import Path

from docopt import docopt
from logbook import NullHandler, StderrHandler

from testbuilder.generate import generate_tests

NullHandler().push_application()
StderrHandler(level="NOTICE").push_application()

# from testbuilder.generate import generate_tests


def main(filename: str) -> None:
    filepath = Path(filename)
    with filepath.open() as io:
        text = io.read()

    depth_s = opts["--unroll-depth"]
    print("depth string", depth_s)
    if depth_s:
        depth = int(depth_s)
    else:
        depth = 10

    test_cases = generate_tests(filepath, text, sys.stdin, depth=depth)
    with open(filepath.stem + "_test.py", "x") as tests:
        tests.write("\n\n".join(test_cases))


if __name__ == "__main__":
    opts = docopt(__doc__)
    main(opts["<source.py>"])
