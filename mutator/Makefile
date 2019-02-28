RUN ?= test
.PHONY: run
run:
	poetry run $(MAKE) test

.PHONY: test
test: pytest clitest

.PHONY: pytest
pytest:
	pytest

.PHONY: clitest
clitest:
	./cli_test


.PHONY: watch
watch:
	git ls-files | poetry run entr -c test.sh $(MAKE) $(RUN)
