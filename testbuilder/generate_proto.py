from ast import AST, parse
from functools import partial
from pathlib import Path
from typing import Any, List, Optional

from logbook import Logger
from toolz import pipe

from . import ssa_basic_blocks as sbb
from .ast_to_ssa import ast_to_ssa
from .function_substituter import FunctionSubstitute
from .iter_monad import liftIter
from .line_splitter import LineSplitter
from .phifilter import PhiFilterer
from .renderer import prompt_and_render_test
from .solver import Solution, solve
from .ssa_repair import repair
from .ssa_to_expression import filter_lines, ssa_to_expression

logger = Logger("generator")


def generate_tests(source: Path, text: str, io: Any, prompt: str = "") -> List[str]:
    def generate_test(module: sbb.Module, target_line: int) -> str:
        request = filter_lines(target_line, module)
        if isinstance(request.code, sbb.BlockTree):
            logger.error(
                f"Couldn't generate a test for line {target_line};"
                " it is not in a function"
            )
            return ""
        function = request.code
        _filter_inputs = partial(filter_inputs, function)

        expr: sbb.TestData = pipe(
            request, repair, PhiFilterer(), FunctionSubstitute(), ssa_to_expression
        )
        solution: Optional[Solution] = solve(expr)
        if not solution:
            logger.error(
                f"Couldn't generate a test for line {target_line};"
                " maybe try increasing the loop unrolling depth?"
            )
            return ""
        _render_test = partial(
            prompt_and_render_test, source, function.name, io, prompt, text, expr
        )
        test: str = pipe(solution, _filter_inputs, _render_test)
        return test

    def parse_file(text: str) -> AST:
        return parse(text, str(source))

    _ast_to_ssa = partial(ast_to_ssa, 10, {})

    module: sbb.Module = pipe(text, parse_file, _ast_to_ssa)
    _generate_test = partial(generate_test, module)

    from .test_utils import write_dot

    write_dot(module, "generated.dot")
    print("lines", LineSplitter()(module))
    return pipe(module, LineSplitter(), liftIter(_generate_test), list)


def filter_inputs(function: sbb.FunctionDef, inputs: Solution) -> Solution:
    args = {}
    for name in function.args:
        args[name] = inputs[name]
    return args
