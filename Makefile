.PHONY: build docs pytest mypy

# From https://stackoverflow.com/a/31605520/2243495
SHELL=/bin/bash -o pipefail

RUN = fastbuild

MYPY = mypy --strict --check-untyped-defs testbuilder/generate.py
export MYPYPATH=./stubs

TESTFILE = testbuilder
# Run pytest
# Args:
#   -ra: Show extra summary information about everything except passing tests
#        at end.
#   --lf Only run tests which failed last time; if no tests failed, run all the
#        tests.
#   --ff Run failed tests before other tests.
#   -x   Stop after first failed test. Speeds up testing runs with failures
#   --maxfail=n Stop after `n` failed tests. This is useful to get a
#        notion of whether we have broken everything or not.
#   -v   Show full diffs.
PYTEST_FLAGS = -x -ra --ff -Wignore
ifdef parallel
	PYTEST = pytest $(PYTEST_FLAGS) -n=$(shell nproc) $(TESTFILE)
else
	PYTEST = pytest $(PYTEST_FLAGS) $(TESTFILE)
endif

build:
	pipenv run $(MYPY)
	pipenv run $(PYTEST)
	./runtests

pytest: PYTEST_FLAGS += --looponfail
pytest:
	pipenv run $(PYTEST) 2>&1 | sed "/seconds ======/,$$ d" | rainbow.py --colorize

mypy:
	pipenv run $(MYPY)

fastbuild:
	$(MYPY)
	$(PYTEST) 2>&1 | sed "/seconds ======/,$$ d" | rainbow.py --colorize
	./runtests

livetest:
	$(MYPY)
	./runtests

run:
	expect run.exp

watch:
	fd ".py|.exp|.tcl" | entr -c test.sh $(MAKE) $(RUN)
test:
	./runtests

# The rest of this makefile is taken from the default Makefile Sphinx makes
# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = pipenv run sphinx-build
SPHINXPROJ    = TestBuilder
SOURCEDIR     = docs
BUILDDIR      = build

help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
docs:
	@$(SPHINXBUILD) -M Makefile "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
