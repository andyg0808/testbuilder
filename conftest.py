import cgitb

import _z3config  # noqa: F401
import logconfig

cgitb.enable()


def pytest_configure(config):
    global verbosity
    verbosity = config.getoption("--verbose")


def pytest_runtest_logstart():
    logconfig.configure_fancylog(verbosity)
