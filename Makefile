.PHONY: build docs

# From https://stackoverflow.com/a/31605520/2243495
SHELL=/bin/bash -o pipefail

MYPY = mypy --strict --check-untyped-defs testbuilder/generate.py
export MYPYPATH=./stubs

# Run pytest
# Args:
#   -ra: Show extra summary information about everything except passing tests
#        at end.
#   --lf Only run tests which failed last time; if no tests failed, run all the
#        tests.
#   --ff Run failed tests before other tests.
#   -x   Stop after first failed test. Speeds up testing runs with failures
#   -v   Show full diffs.
PYTEST = pytest -x -ra --ff testbuilder

build:
	pipenv run $(MYPY)
	pipenv run $(PYTEST)
	./runtests

fastbuild:
	$(MYPY)
	$(PYTEST) | rainbow.py --colorize
	./runtests

run:
	expect run.exp

watch:
	fd ".py|.exp|.tcl" | entr -c test.sh $(MAKE) fastbuild
test:
	./test.sh

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
