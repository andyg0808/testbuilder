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

.PHONY: build
build:
	pipenv run $(MAKE) $(RUN)

.PHONY: watch
watch:
	fd ".py|.exp|.tcl" | entr -c test.sh $(MAKE) $(RUN)

.PHONY: fastbuild
fastbuild: mypy pytest runtests snippets

.PHONY: livetest
livetest: mypy runtests snippets

.PHONY: mypy
mypy:
	$(MYPY)

.PHONY: pytest
pytest: PYTEST_FLAGS += --looponfail
pytest:
	$(PYTEST) 2>&1 | unbuffer rainbow.py --colorize

.PHONY: plaintest
plaintest:
	$(PYTEST)

.PHONY: runtests
runtests:
	./runtests

.PHONY: snippets
snippets:
	./run_on_snippets

.PHONY: docs
docs:
	pipenv run sphinx-apidoc --separate --force --o docs/api testbuilder
	pipenv run sphinx-build -b html docs build

.PHONY: doc-server
doc-server:
	python -m http.server --directory build

.PHONY: clean
clean:
	rm -r build
