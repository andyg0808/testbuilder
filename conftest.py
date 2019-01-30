import cgitb
import os
import re

import logbook

import rainbow

cgitb.enable()

Replacer = rainbow.Replacer(colorize=True)
LoggerName = re.compile(r"")


def pytest_configure(config):
    global verbosity
    verbosity = config.getoption("--verbose")


FILES = {"conditional_elimination": logbook.INFO}


def should_write(r, h):
    level = FILES.get(r.channel, None)
    if level is None:
        return False
    return level <= r.level


def rainbowize(record):
    record.message = Replacer.color(record.message)


def pytest_runtest_logstart():
    from logbook import StderrHandler, NullHandler, Processor

    null_handler = NullHandler()
    null_handler.push_application()

    if os.environ.get("VERBOSE", False) or verbosity:
        flag = os.environ.get("VERBOSE", False)
        ignores = os.environ.get("IGNORE", "").split(",")
        if flag and flag.isnumeric():
            StderrHandler(
                level=int(flag), filter=lambda r, h: r.channel not in ignores
            ).push_application()
        elif flag and LoggerName.match(flag):
            print(f"Only logging from {flag}")
            StderrHandler(filter=lambda r, h: r.channel == flag).push_application()
        else:
            StderrHandler().push_application()
        return

    stderr_handler = StderrHandler(level="WARNING")
    stderr_handler.push_application()

    stderr_handler = StderrHandler(filter=should_write)
    stderr_handler.push_application()

    level = os.environ.get("LEVEL", False)
    if level:
        log_name = os.environ.get("NAME", False)
        if log_name:
            stderr_handler = StderrHandler(
                level=level, filter=lambda r, h: r.channel == log_name
            )
        else:
            stderr_handler = StderrHandler(level=level)

            stderr_handler.push_application()
    Processor(rainbowize).push_application()
