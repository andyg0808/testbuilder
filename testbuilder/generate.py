import re
from ast import AST, parse
from functools import partial
from pathlib import Path
from typing import Any, Iterable, List, Optional, Set, Tuple, Union

from logbook import Logger
from toolz import concat, pipe

from . import ssa_basic_blocks as sbb, utils
from .ast_to_ssa import ast_to_ssa
from .converter import TupleError
from .dataclass_utils import make_extended_instance
from .expr_stripper import ExprStripper
from .function_substituter import FunctionSubstitute
from .iter_monad import liftIter
from .line_splitter import line_splitter
from .linefilterer import filter_lines
from .phifilter import PhiFilterer
from .preprocessor import AutoPreprocessor, ChangeList, Preprocessor
from .renderer import get_test_func, prompt_for_test, render_test, run_for_test
from .requester import Requester
from .solver import Solution, solve
from .ssa_repair import repair
from .ssa_to_expression import ssa_to_expression
from .type_builder import TypeBuilder
from .type_registrar import TypeRegistrar

log = Logger("generator")


def generate_tests(
    source: Path,
    text: str,
    requester: Requester,
    *,
    changes: Optional[ChangeList] = None,
    prompt: str = "",
    depth: int = 10,
    lines: Optional[Set[int]] = None,
    autogen: bool = False,
) -> List[str]:
    def generate_test(
        registrar: TypeRegistrar, module: sbb.Module, target_info: Tuple[int, int]
    ) -> str:
        test_number, target_line = target_info
        request = filter_lines(target_line, module)
        if request is None:
            log.error(
                f"Couldn't generate a test for line {target_line};"
                " it likely is either dead code or a line number"
                " which doesn't exist."
            )
            return ""
        if isinstance(request.code, sbb.BlockTree):
            log.error(
                f"Couldn't generate a test for line {target_line};"
                " it is not in a function"
            )
            return ""
        function = request.code

        cleaned_expr: sbb.Request = pipe(
            request, repair, PhiFilterer(), FunctionSubstitute(), ExprStripper()
        )
        assert isinstance(cleaned_expr, sbb.Request)
        log.debug(
            "\n=====Cleaned expression=====\n"
            + utils.dataclass_dump(cleaned_expr)
            + "\n=====END cleaned expression====="
        )
        try:
            testdata = ssa_to_expression(source, registrar, cleaned_expr)
        except TupleError:
            return ""
        except RuntimeError as e:
            log.error(
                "Caught error while generating test for line {}. Error:\n\t{}",
                target_line,
                str(e),
            )
            return ""
        solution: Optional[Solution] = solve(registrar, testdata)
        if not solution:
            log.error(
                f"Couldn't generate a test for line {target_line};"
                " maybe try increasing the loop unrolling depth?"
            )
            log.debug(f"Couldn't solve {testdata.expression}")
            return ""
        _filter_inputs = partial(filter_inputs, function)

        def get_expected_test_result(args: sbb.Solution) -> sbb.ExpectedTestData:
            updated_testdata = make_extended_instance(
                testdata,
                sbb.SolvedTestData,
                args=args,
                test_number=test_number,
                target_line=target_line,
            )
            if autogen:
                func = get_test_func(updated_testdata)
                return run_for_test(requester, func, updated_testdata)
            else:
                return prompt_for_test(
                    requester=requester, prompt=prompt, test=updated_testdata
                )

        test: str = pipe(
            solution, _filter_inputs, get_expected_test_result, render_test
        )
        return test

    def parse_file(text: str) -> AST:
        if changes:
            preprocess: Preprocessor = AutoPreprocessor(text, changes)
        else:
            preprocess = Preprocessor(text)
        return preprocess(parse(text, str(source)))

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
    log.debug("\n=====SSA module=====\n{}\n=====END SSA module=====", module)
    builder = TypeBuilder()
    registrar = builder.construct()
    _generate_test = partial(generate_test, registrar, module)

    def generate_unit_tests(unit: Union[sbb.FunctionDef, sbb.BlockTree]) -> List[str]:
        splits: Iterable[int]
        if lines is not None:
            _filter = partial(filter, lambda x: x in lines)
            splits = pipe(unit, LineSplitter(), _filter)  # type: ignore
        else:
            splits = pipe(unit, LineSplitter())
        # Filter out blank tests. These are the tests which were
        # ignored for some reason (e.g., we couldn't find a solution
        # or they had unsupported code in their function.)
        _drop_blank = partial(filter, lambda x: x)
        return pipe(  # type: ignore
            splits, enumerate, liftIter(_generate_test), _drop_blank, list
        )

    log.debug("Splitting on lines", LineSplitter()(module))
    return pipe(  # type: ignore
        module, function_splitter, liftIter(generate_unit_tests), concat, list
    )


def filter_inputs(function: sbb.FunctionDef, inputs: Solution) -> Solution:
    args = {}
    for name in function.args:
        args[name] = inputs.get(name, default_value(name))
    return args


def default_value(name: str) -> Any:
    return 1_234_567_890
