RUN ?= test
.PHONY: run
run:
	poetry run $(MAKE) test

.PHONY: test
test: mypy pytest clitest run_test

.PHONY: mypy
mypy:
	mypy --strict bin/run_test

.PHONY: pytest
pytest:
	pytest mutator_test.py

.PHONY: clitest
clitest:
	./cli_test

.PHONY: run_test
run_test:
	bin/run_test 'pytest testcase.py' . testcase.py mutator_test.py mutator_test_example.py


.PHONY: watch
watch:
	git ls-files | poetry run entr -c test.sh $(MAKE) $(RUN)
