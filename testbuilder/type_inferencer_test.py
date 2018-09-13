import ast
from functools import partial

from toolz import pipe

from .ast_to_ssa import ast_to_ssa
from .type_inferencer import TypeInferencer
from .vartypes import Type


def check_expression(code, type, depth=10):
    _ast_to_ssa = partial(ast_to_ssa, depth, {})
    ssa_tree = pipe(code.strip(), ast.parse, _ast_to_ssa)
    code_type = TypeInferencer()(ssa_tree)
    assert code_type == type


def test_int():
    check_expression("2", Type.int)
