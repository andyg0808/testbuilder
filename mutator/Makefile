RUN ?= test
.PHONY: run
run:
	poetry run $(MAKE) test

.PHONY: test
test: mypy pytest clitest

.PHONY: mypy
mypy:
	mypy --strict run_test

.PHONY: pytest
pytest:
	pytest

.PHONY: clitest
clitest:
	./cli_test


.PHONY: watch
watch:
	git ls-files | poetry run entr -c test.sh $(MAKE) $(RUN)
