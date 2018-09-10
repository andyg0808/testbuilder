import ast
from pathlib import Path
from sys import stderr
from typing import Any, List, Mapping, Optional
from unicodedata import normalize

from logbook import Logger, StreamHandler  # type: ignore

from .build_tree import build_tree
from .expression_builder import Expression, ExpressionBuilder
from .function_walker import FunctionWalker
from .renderer import render_test
from .slicing import Dependency, Slicer
from .solver import Solution, solve

logger = Logger("generator")


class TestConstructor:
    def __init__(self, source: Path, function: ast.FunctionDef) -> None:
        self.source = source
        self.function = function
        logger.notice("Processing {}", ast.dump(self.function))
        self.slicer = Slicer(self.function)
        self.block_tree = build_tree(self.function)

    def get_expression(self, dep_tree: Dependency, depth: int = 1) -> Expression:
        variables = dep_tree.get_slice_variables()
        flowgraph = self.block_tree.inflate(dep_tree)
        builder = ExpressionBuilder(depth)
        return builder.get_expression(variables, flowgraph)

    def solve_expression(self, expression: Expression) -> Optional[Solution]:
        return solve(expression)

    def generate_test(self, inputs: Solution, expected: str) -> str:
        return render_test(self.source, self.function.name, inputs, expected)

    def find_inputs(self, dep_tree: Dependency) -> Solution:
        expression = self.get_expression(dep_tree)
        solution = self.solve_expression(expression)
        if not solution:
            raise UnsolvableExpressionException()
        return self.filter_inputs(solution)

    def slice_to_test(self, dep_tree: Dependency, io: Any, prompt: str = "") -> str:
        try:
            inputs = self.find_inputs(dep_tree)
        except UnsolvableExpressionException:
            logger.error(
                f"Couldn't generate a test for line {dep_tree.lineno}; \
                  maybe try increasing the loop unrolling depth?"
            )
            return ""

        if prompt == "":
            print(f"What is the expected output from these arguments? {inputs}")
        expected = io.readline()
        return self.generate_test(inputs, expected)

    def generate_all(self, io: Any, prompt: str = "") -> List[str]:
        statements = self.slicer.statements()
        return [self.slice_to_test(statement, io, prompt) for statement in statements]

    def filter_inputs(self, inputs: Solution) -> Solution:
        args = {}
        for arg in self.function.args.args:
            name = arg.arg
            args[name] = inputs[name]
        return args


def generate_tests(source: Path, text: str, io: Any, prompt: str = "") -> List[str]:
    tree = ast.parse(text)
    walker = FunctionWalker()
    walker.visit(tree)
    tests: List[str] = []
    for function in walker:
        c = TestConstructor(source, function)
        tests += c.generate_all(io, prompt)
    return tests


def run_test(func_name: str, code_string: str) -> None:
    loc: Any = {}
    normalized = normalize("NFKC", func_name)
    exec(code_string, loc, loc)
    loc[normalized]()


class UnsolvableExpressionException(RuntimeError):
    pass
