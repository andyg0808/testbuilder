"""
Provides get_expression function to extract a controlling slice of code for the
value at a given line.
"""
import ast
from functools import partial
from typing import Optional

from toolz import pipe

import z3

from .ast_to_ssa import ast_to_ssa
from .basic_block import BasicBlock
from .slicing import take_slice
from .ssa_basic_blocks import TestData
from .ssa_to_expression import ssa_lines_to_expression
from .type_registrar import TypeRegistrar
from .utils import pipe_print

NULL = z3.DeclareSort("None")


StopBlock = Optional[BasicBlock]


def get_expression(
    registrar: TypeRegistrar, line: int, code: ast.AST, depth: int = 1
) -> Optional[TestData]:
    dep_tree = take_slice(line, code)
    if not dep_tree:
        return None
    _ast_to_ssa = partial(ast_to_ssa, depth, {})
    _ssa_to_expression = partial(ssa_lines_to_expression, registrar, dep_tree.lineno)
    return pipe(code, _ast_to_ssa, pipe_print, _ssa_to_expression)
