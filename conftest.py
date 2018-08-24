import os
def pytest_configure(config):
    global verbosity
    verbosity = config.getoption('--verbose')


def pytest_runtest_logstart():
    from logbook import StderrHandler, NullHandler
    import logbook
    null_handler = NullHandler()
    null_handler.push_application()
    stderr_handler = StderrHandler(level='WARNING')
    stderr_handler.push_application()
    if os.environ.get('VERBOSE', False) or verbosity:
        StderrHandler().push_application()
