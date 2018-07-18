#!/usr/bin/env python3
"""
generate_test_cases: Generates test cases for the return values of all functions in <filename>

Usage: run.py <filename>

Options:
    <filename>  The file for which to generate test cases.
"""

import sys
from pathlib import Path

from docopt import docopt

from testbuilder.generate import generate_tests


def main(filename: str) -> None:
    filepath = Path(filename)
    with filepath.open() as io:
        text = io.read()
    test_cases = generate_tests(filepath, text, sys.stdin)
    with open(filepath.stem + "_test.py", "x") as tests:
        tests.write("\n\n".join(test_cases))


if __name__ == "__main__":
    opts = docopt(__doc__)
    main(opts["<filename>"])
