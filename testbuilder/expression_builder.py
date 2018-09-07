"""
Provides get_expression function to extract a controlling slice of code for the
value at a given line.
"""
import ast
from copy import copy
from functools import partial, reduce
from typing import (
    Callable,
    Iterable,
    List,
    Mapping,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from toolz import pipe

import z3
from typeassert import assertify

from . import basic_block
from .ast_builder import make_ast
from .basic_block import BasicBlock, BlockTree
from .build_tree import RETURNBLOCK, build_tree
from .converter import VAR_START_VALUE, convert, get_variable
from .slicing import Variable, take_slice

NULL = z3.DeclareSort("None")


VarMapping = MMapping[str, int]
StopBlock = Optional[BasicBlock]

Expression = z3.ExprRef
ExprList = List[Expression]


def _simplify_logical(
    exprs: Tuple[Expression, ...], function: Callable[..., Expression]
) -> Expression:
    if len(exprs) > 1:
        return function(*exprs)
    else:
        return exprs[0]


def bool_not(expr: Expression) -> Expression:
    return z3.Not(expr)


def bool_or(*exprs: Expression) -> Expression:
    return _simplify_logical(exprs, z3.Or)


def bool_and(*exprs: Expression) -> Expression:
    return _simplify_logical(exprs, z3.And)


def get_expression(line: int, code: ast.AST, depth: int = 1) -> Optional[Expression]:
    # block_tree = build_tree(code)
    dep_tree = take_slice(line, code)
    if not dep_tree:
        return None
    # tree = block_tree.inflate(dep_tree)
    variables = dep_tree.get_slice_variables()
    eb = ExpressionBuilder(depth, dep_tree.lineno, dep_tree.lines())
    return eb.get_expression(variables, code)


class ExpressionBuilder:
    def __init__(self, depth: int, target_line: int, lines: Set[int]) -> None:
        self.depth = depth
        self.lines = lines
        self.target_line = target_line

    def get_expression(
        self, variables: Iterable[Variable], code: ast.AST
    ) -> Expression:
        # Sets variables to the default value, to treat them as having been defined
        # before the blocks begin. Mostly important for handling function
        # arguments.
        mutation_counts = {v.code: VAR_START_VALUE for v in variables}
        return self.convert_tree(code, mutation_counts)

    def convert_tree(self, code: ast.AST, variables: VarMapping) -> Expression:
        # assert tree.target
        # print("target", tree.target, tree.target.number)
        # expr_list = self._convert_target_tree(tree.target, None, copy(variables), None)
        # expected = _combine_conditions(expr_list)
        actual = self._modern_convert_tree(copy(variables), code)
        print("Actual expression:", actual)
        # print("Expression from old code:", expected)
        return actual

    def _modern_convert_tree(self, variables: VarMapping, code: ast.AST) -> Expression:
        from .ast_to_ssa import ast_to_ssa

        from .ssa_to_expression import ssa_lines_to_expression
        from toolz import pipe
        from functools import partial
        from .ssa_basic_blocks import TestData

        _ast_to_ssa = partial(ast_to_ssa, self.depth, variables)
        _ssa_to_expression = partial(
            ssa_lines_to_expression, self.target_line, self.lines
        )

        from .utils import pipe_print

        variables = {}
        testdata: TestData = pipe(code, _ast_to_ssa, pipe_print, _ssa_to_expression)
        return testdata.expression


def to_boolean(expr: Expression) -> Expression:
    if z3.is_int(expr):
        return expr == z3.IntVal(0)
    elif z3.is_bool(expr):
        return expr
    else:
        raise UnknownConversionException(
            f"Can't convert {expr.sort().name()} to boolean"
        )


class UnknownConversionException(RuntimeError):
    pass


def _is_required(
    root: BasicBlock,
    stop_at: Optional[BasicBlock],
    seen: Optional[Set[BasicBlock]] = None,
) -> bool:
    """
    Returns true if a child of root is required
    """
    if not seen:
        seen = set()

    if root in seen:
        return False
    else:
        seen.add(root)

    if root is stop_at:
        return False
    if root.required:
        return True
    for child in root.children:
        if _is_required(child, stop_at, seen):
            return True

    return False


def _update_paths(
    paths: List[Tuple[ExprList, VarMapping]]
) -> Tuple[List[ExprList], VarMapping]:
    variables, edit_lists = unify_all_variables([p[1] for p in paths])
    updated_conditions = []
    for path, edit_list in zip(paths, edit_lists):
        updated_conditions.append(path[0] + edit_list)
    return (updated_conditions, variables)


def _combine_conditions(conds: Sequence[Expression]) -> Expression:
    if len(conds) > 1:
        return bool_and(*conds)
    else:
        return conds[0]


def unify_all_variables(
    variable_lists: Sequence[Mapping[str, int]]
) -> Tuple[MMapping[str, int], List[ExprList]]:
    """
        Args:
            variable_lists: A list of mappings from variable names to use counts.

        Returns:
            A tuple of a new variable mapping and a list of additional
            expressions to add to each of the expression lists associated with
            the variable_lists passed in. The list of additional expressions is in the same order as the lists in variable_lists
        """
    if not variable_lists:
        return ({}, [])
    available_variables = (x.keys() for x in variable_lists)
    keys = reduce(lambda x, y: x | y, available_variables)
    renamings: List[ExprList] = [[] for i in variable_lists]
    variables = {}
    first = variable_lists[0]
    for key in sorted(keys):
        # Handle the special case where all the variable lists have the same value. We don't want to waste time on fancy things then.
        if key in first:
            expected = first[key]
            if all(lambda x: key in x and x[key] == expected for x in variable_lists):
                variables[key] = expected
                next
        max_value = max(x.get(key, 0) for x in variable_lists)
        next_name = get_variable(key, max_value)
        dest = z3.Int(next_name)
        for var_list, var_renaming in zip(variable_lists, renamings):
            if key in var_list and var_list[key] != max_value:
                name = get_variable(key, var_list[key])
                source = z3.Int(name)
                var_renaming.append(dest == source)
        variables[key] = max_value

    return (variables, renamings)
