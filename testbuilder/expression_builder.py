"""
Provides get_expression function to extract a controlling slice of code for the
value at a given line.
"""
import ast
from functools import partial
from pathlib import Path
from typing import Optional

from toolz import pipe

import z3

from .ast_to_ssa import ast_to_ssa
from .ssa_basic_blocks import TestData
from .ssa_to_expression import ssa_lines_to_expression
from .type_registrar import TypeRegistrar

NULL = z3.DeclareSort("None")


def get_expression(
    registrar: TypeRegistrar,
    filepath: Path,
    line: int,
    code: ast.AST,
    depth: int = 1,
    slice: bool = True,
) -> Optional[TestData]:
    _ast_to_ssa = partial(ast_to_ssa, depth, {})
    _ssa_to_expression = partial(
        ssa_lines_to_expression, filepath, registrar, line, slice
    )
    return pipe(code, _ast_to_ssa, _ssa_to_expression)
