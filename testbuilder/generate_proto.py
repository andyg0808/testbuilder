from ast import AST, FunctionDef, parse
from functools import partial, reduce
from pathlib import Path
from sys import stderr
from typing import (
    Any,
    Callable,
    Generic,
    Iterator,
    List,
    Mapping,
    Optional,
    TypeVar,
    cast,
)

from logbook import Logger, StreamHandler  # type: ignore
from toolz import compose, pipe

from dataclasses import dataclass

from .build_tree import build_tree
from .expression_builder import Expression, ExpressionBuilder
from .function_walker import split_functions
from .iter_monad import chain, liftIter, optional_to_iter, returnIter
from .renderer import prompt_and_render_test
from .slicing import FuncStmt, Statement, split_statements
from .solver import Solution, solve

StreamHandler(stderr).push_application()
logger = Logger("generator")


def generate_tests(source: Path, text: str, io: Any, prompt: str = "") -> List[str]:
    def build_test_case(funcstmt: FuncStmt) -> str:
        _filter_inputs = partial(filter_inputs, funcstmt.function)
        _render_test = partial(
            prompt_and_render_test,
            source,
            funcstmt.function.name,
            io,
            prompt,
            text,
            funcstmt.function,
        )
        solution: Optional[Solution] = pipe(funcstmt, get_expression, solve)
        if not solution:
            logger.error(
                f"Couldn't generate a test for line {funcstmt.statement.lineno}; \
                  maybe try increasing the loop unrolling depth?"
            )
            return ""
        test: str = pipe(solution, _filter_inputs, _render_test)
        return test

    def parse_file(text: str) -> AST:
        # print("text", text)
        return parse(text, str(source))

    return pipe(
        returnIter(text),
        liftIter(parse_file),
        chain(split_statements, split_functions),
        liftIter(build_test_case),
        list,
    )


def filter_inputs(function: FunctionDef, inputs: Solution) -> Solution:
    args = {}
    for arg in function.args.args:
        name = arg.arg
        args[name] = inputs[name]
    return args


def get_expression_at_depth(depth: int, funcstmt: FuncStmt) -> Expression:
    variables = funcstmt.statement.get_slice_variables()
    block_tree = build_tree(funcstmt.function)
    flowgraph = block_tree.inflate(funcstmt.statement)
    builder = ExpressionBuilder(depth, funcstmt.statement.lines())
    return builder.get_expression(variables, flowgraph)


get_expression = partial(get_expression_at_depth, 2)


# @dataclass
# class StateM(Generic[A, B]):
#     state: A
#     value: B


# FuncState = StateM[FunctionDef, A]
# S = TypeVar("S")


# def liftState(func: Callable[[A], B]) -> Callable[[StateM[S, A]], StateM[S, B]]:
#     def _lift(state: StateM[S, A]) -> StateM[S, B]:
#         return StateM(state.state, func(state.value))

#     return _lift
