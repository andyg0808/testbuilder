from ast import AST, parse
from functools import partial
from pathlib import Path
from typing import Any, List, Optional, Set, Tuple, Union

from logbook import Logger
from toolz import concat, pipe

from . import ssa_basic_blocks as sbb
from .ast_to_ssa import ast_to_ssa
from .expr_stripper import ExprStripper
from .function_substituter import FunctionSubstitute
from .iter_monad import liftIter
from .line_splitter import LineSplitter
from .phifilter import PhiFilterer
from .renderer import prompt_and_render_test
from .solver import Solution, solve
from .ssa_repair import repair
from .ssa_to_expression import filter_lines, ssa_to_expression
from .type_builder import TypeBuilder
from .type_registrar import TypeRegistrar
from .utils import WriteDot

logger = Logger("generator")


def generate_tests(
    source: Path,
    text: str,
    io: Any,
    *,
    prompt: str = "",
    depth: int = 10,
    lines: Optional[Set[int]] = None,
) -> List[str]:
    def generate_test(
        registrar: TypeRegistrar, module: sbb.Module, target_info: Tuple[int, int]
    ) -> str:
        test_number, target_line = target_info
        request = filter_lines(target_line, module)
        if isinstance(request.code, sbb.BlockTree):
            logger.error(
                f"Couldn't generate a test for line {target_line};"
                " it is not in a function"
            )
            return ""
        function = request.code
        _ssa_to_expression = partial(ssa_to_expression, registrar)

        expr: sbb.TestData = pipe(
            request,
            repair,
            PhiFilterer(),
            FunctionSubstitute(),
            ExprStripper(),
            WriteDot("generate.dot"),
            _ssa_to_expression,
        )
        solution: Optional[Solution] = solve(registrar, expr)
        if not solution:
            logger.error(
                f"Couldn't generate a test for line {target_line};"
                " maybe try increasing the loop unrolling depth?"
            )
            logger.debug(f"Couldn't solve {expr}")
            return ""
        _filter_inputs = partial(filter_inputs, function)
        _render_test = partial(
            prompt_and_render_test,
            source,
            function.name,
            io,
            prompt,
            text,
            expr,
            test_number,
        )
        test: str = pipe(solution, _filter_inputs, _render_test)
        return test

    def parse_file(text: str) -> AST:
        return parse(text, str(source))

    def function_splitter(
        module: sbb.Module
    ) -> List[Union[sbb.BlockTree, sbb.FunctionDef]]:
        items: List[Union[sbb.BlockTree, sbb.FunctionDef]] = list(
            module.functions.values()
        )
        items.append(module.code)
        return items

    _ast_to_ssa = partial(ast_to_ssa, depth, {})

    module: sbb.Module = pipe(text, parse_file, _ast_to_ssa)
    builder = TypeBuilder()
    registrar = builder.construct()
    _generate_test = partial(generate_test, registrar, module)

    def generate_unit_tests(unit: Union[sbb.FunctionDef, sbb.BlockTree]) -> List[str]:
        if lines is not None:
            _filter = partial(filter, lambda x: x in lines)
            return pipe(
                unit, LineSplitter(), _filter, enumerate, liftIter(_generate_test), list
            )
        else:
            return pipe(unit, LineSplitter(), enumerate, liftIter(_generate_test), list)

    print("lines", LineSplitter()(module))
    return pipe(module, function_splitter, liftIter(generate_unit_tests), concat, list)


def filter_inputs(function: sbb.FunctionDef, inputs: Solution) -> Solution:
    args = {}
    for name in function.args:
        args[name] = inputs.get(name, default_value(name))
    return args


def default_value(name: str) -> Any:
    return 1234567890
