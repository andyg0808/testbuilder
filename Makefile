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
#   --duration=n Show the `n` slowest tests.
PYTEST_FLAGS = -x -ra -Wignore
PYTEST_FAST_FLAGS = $(PYTEST_FLAGS) --last-failed --last-failed-no-failures none -p no:ordering
ifdef remote
PYTEST_COMPLETE_FLAGS = $(PYTEST_FLAGS) --duration=5 -d --tx=socket=$(remote):888{0..9} --rsyncdir $(TESTFILE) $(TESTFILE)
else
PYTEST_COMPLETE_FLAGS = $(PYTEST_FLAGS) --duration=5 -n=$(shell nproc)
endif
PYTEST_COMPLETE = pytest $(PYTEST_COMPLETE_FLAGS) $(TESTFILE)
PYTEST_FAST = ./pytest_empty $(PYTEST_FAST_FLAGS) $(TESTFILE)

.PHONY: build
build:
	pipenv run $(MAKE) $(RUN)

.PHONY: watch
watch:
	fd ".py|.exp|.tcl|Makefile" | entr -c test.sh $(MAKE) $(RUN)

.PHONY: fastbuild
fastbuild: mypy pytest runtests snippets

.PHONY: livetest
livetest: mypy runtests snippets

.PHONY: mypy
mypy:
	$(MYPY)

.PHONY: pytest
pytest:
	$(PYTEST_FAST)
	$(PYTEST_COMPLETE)

.PHONY: plaintest
plaintest:
	$(PYTEST)

.PHONY: runtests
runtests:
	./runtests

.PHONY: snippets
snippets:
	cd private && $(MAKE)

.PHONY: docs
docs:
	pipenv run sphinx-apidoc --separate --force --o docs/api testbuilder
	pipenv run sphinx-build -b html docs build

.PHONY: doc-server
doc-server:
	python -m http.server --directory build

.PHONY: clean
clean:
	rm -rf build
	rm -rf .pytest_cache
