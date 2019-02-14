#!/usr/bin/env python3
import cProfile
import csv
import io
import json
import signal
import timeit
from pathlib import Path
from typing import Set

import typeassert
from docopt import docopt
from logbook import NullHandler

import _z3config  # noqa: F401
import logconfig
from testbuilder.generate import generate_tests
from testbuilder.requester import Requester

Docs = """
profiling_run: Profile testbuilder

Usage: profiling_run.py [options] <source.py>

Options:
    --ignore=<line,line>  Do not generate tests for the specified lines
"""


def signal_handler(num, f):
    import traceback

    traceback.print_stack()
    breakpoint()
    return


signal.signal(signal.SIGUSR1, signal_handler)

pr = cProfile.Profile()
pr.enable()


def save_profile(num, f):
    pr.disable()
    pr.dump_stats("fullprofile")
    return


signal.signal(signal.SIGUSR2, save_profile)


typeassert.log.setLevel("ERROR")


def main(filename: str, ignores: Set[int]) -> None:
    filepath = Path(filename)
    with filepath.open() as infile:
        text = infile.read()
    requester = Requester()
    with open("private/autopreprocess.json") as json_file:
        changes = json.load(json_file)
    glob = dict(globals())
    glob.update(locals())
    timer = timeit.Timer(
        "generate_tests(filepath, text, requester, depth=10, autogen=True, changes=changes, ignores=ignores)",
        globals=glob,
    )
    times = timer.repeat(repeat=1, number=1)
    print(f"Total time: {times}")
    with open("profiling_log.csv", mode="a", newline="") as fi:
        fi.seek(io.SEEK_END)
        dataset = csv.writer(fi)
        dataset.writerow(times)


if __name__ == "__main__":
    opts = docopt(Docs)

    NullHandler().push_application()
    logconfig.configure_fancylog(None)

    ignores_s = opts["--ignore"]
    if ignores_s:
        ignores = set(ignores_s.split(","))
    else:
        ignores = set()

    main(opts["<source.py>"], ignores)
    # Save current profile data when run finishes
    save_profile(0, None)
