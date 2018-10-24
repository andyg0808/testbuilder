"""
Provides get_expression function to extract a controlling slice of code for the
value at a given line.
"""
import ast
from copy import copy
from functools import partial, reduce
from typing import (
    List,
    Mapping,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

import z3
from toolz import pipe

from .ast_to_ssa import ast_to_ssa
from .basic_block import BasicBlock
from .converter import get_variable
from .slicing import take_slice
from .ssa_basic_blocks import TestData
from .ssa_to_expression import Expression, ExprList, ssa_lines_to_expression
from .utils import pipe_print
from .variable_manager import VarMapping
from .z3_types import bool_and

NULL = z3.DeclareSort("None")


StopBlock = Optional[BasicBlock]


def get_expression(line: int, code: ast.AST, depth: int = 1) -> Optional[TestData]:
    dep_tree = take_slice(line, code)
    if not dep_tree:
        return None
    eb = ExpressionBuilder(depth, dep_tree.lineno)
    return eb.get_expression(code)


class ExpressionBuilder:
    def __init__(self, depth: int, target_line: int) -> None:
        self.depth = depth
        self.target_line = target_line

    def get_expression(self, code: ast.AST) -> TestData:
        return self.convert_tree(code, {})

    def convert_tree(self, code: ast.AST, variables: VarMapping) -> TestData:
        actual = self._modern_convert_tree(copy(variables), code)
        return actual

    def _modern_convert_tree(self, variables: VarMapping, code: ast.AST) -> TestData:

        _ast_to_ssa = partial(ast_to_ssa, self.depth, variables)
        _ssa_to_expression = partial(ssa_lines_to_expression, self.target_line)

        testdata: TestData = pipe(code, _ast_to_ssa, pipe_print, _ssa_to_expression)
        return testdata
