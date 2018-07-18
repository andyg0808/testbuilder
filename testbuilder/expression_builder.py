"""
Provides get_expression function to extract a controlling slice of code for the
value at a given line.
"""
import ast
from copy import copy
from functools import reduce
from typing import (
    Any,
    Iterable,
    Iterator,
    List,
    Mapping,
    MutableMapping as MMapping,
    NewType,
    Optional,
    Sequence,
    Set,
    Tuple,
    cast,
)

import z3

from . import basic_block
from .basic_block import BasicBlock
from .build_tree import build_tree
from .converter import VAR_START_VALUE, convert, get_variable
from .slicing import Dependency, Variable, take_slice

NULL = z3.DeclareSort("None")


VarMapping = MMapping[str, int]
StopBlock = Optional[BasicBlock]

Expression = z3.ExprRef
ExprList = List[Expression]


def get_expression(code: ast.AST, line: int, depth: int = 1) -> Optional[Expression]:
    block_tree = build_tree(code)
    dep_tree = take_slice(code, line)
    print("dep_tree", dep_tree, "end")
    if not dep_tree:
        return None
    flowgraph = block_tree.inflate(dep_tree)
    eb = ExpressionBuilder(depth)
    variables = get_slice_variables(dep_tree)
    return eb.get_expression(variables, flowgraph)


def get_slice_variables(dep_tree: Dependency) -> Iterator[Variable]:
    """
    Find all Variable instances in a dependency tree.
    """
    slice_tree = dep_tree.format_slice()
    variables = filter(lambda x: isinstance(x, Variable), slice_tree)
    return cast(Iterator[Variable], variables)


class ExpressionBuilder:
    def __init__(self, depth: int) -> None:
        self.depth = depth

    def get_expression(
        self, variables: Iterable[Variable], flowgraph: BasicBlock
    ) -> Expression:
        expr_list: ExprList = self.convert_tree(flowgraph, variables)
        return _combine_conditions(expr_list)

    def convert_tree(self, root: BasicBlock, variables: Iterable[Variable]) -> ExprList:
        # Sets variables to the default value, to treat them as having been defined
        # before the blocks begin. Mostly important for handling function
        # arguments.
        mutation_counts = {v.code: VAR_START_VALUE for v in variables}
        return self._convert_block_tree(root, mutation_counts, None)

    def _convert_block_tree(
        self, root: BasicBlock, variables: VarMapping, stop: StopBlock = None
    ) -> ExprList:
        """
        Args:
            root: The BasicBlock to start at
            variables: A mapping from variable name to the number of times the
                       variable has been used. This is for tracking mutations.
            stop: An optional BasicBlock at which to break tree processing. Is
                  not considered in the processing at all. This is used to
                  handle processing only the forked part of if statements.
        """
        if root is stop:
            return []

        if root.type == basic_block.Loop:
            return self._convert_loop(root, variables, stop)
        elif root.type == basic_block.Conditional:
            return self._convert_conditional(root, variables, stop)
        elif root.type == basic_block.Code:
            return self._convert_code_block(root, variables, stop)
        raise RuntimeError(f"Unknown block type: {root.type}")

    def _convert_loop(
        self, root: BasicBlock, variables: VarMapping, stop: StopBlock
    ) -> ExprList:
        def construct_path(
            path: ExprList, path_vars: VarMapping, returns: bool
        ) -> Tuple[ExprList, VarMapping]:
            path = copy(path)
            path_vars = copy(path_vars)
            # Make typechecker happy. This should always be true of loops.
            assert root.conditional
            if not returns:
                path.append(
                    z3.Not(to_boolean(convert(root.conditional.code, path_vars)))
                )
            return (path, path_vars)

        assert root.type == basic_block.Loop

        body, bypass = root.children

        if _is_required(body, root):
            # We can't bypass the loop: the body is required
            paths: List[Tuple[ExprList, VarMapping]] = []
        elif root.conditional is None:
            return self._convert_block_tree(bypass, variables, stop)
        elif body.returns:
            code = [z3.Not(to_boolean(convert(root.conditional.code, variables)))]
            code += self._convert_block_tree(bypass, variables, stop)
            return code
        else:
            paths = [construct_path([], variables, body.returns)]

        # Make typechecker happy. This should always be true of loops.
        assert root.conditional

        # If the body returns, never iterate more than once!
        if body.returns:
            depth = 1
        else:
            depth = self.depth

        loops: ExprList = []
        for _i in range(depth):
            print("start variables", variables, "for loop", _i)
            loops += [to_boolean(convert(root.conditional.code, variables))]
            loops += self._convert_block_tree(body, variables, root)
            print("variables", variables, "for loop", _i)
            paths.append(construct_path(loops, variables, body.returns))

        updated_conditions, updated_variables = _update_paths(paths)
        variables.clear()
        variables.update(updated_variables)

        conditions = [_combine_conditions(code) for code in updated_conditions]
        if len(conditions) > 1:
            code = [z3.Or(*conditions)]
        elif len(conditions) == 1:
            code = [conditions[0]]
        else:
            raise RuntimeError("No conditions!")

        code += self._convert_block_tree(bypass, variables, stop)
        return code

    def _convert_conditional(
        self, root: BasicBlock, variables: VarMapping, stop: StopBlock
    ) -> ExprList:
        def construct_branch(
            child: BasicBlock, join: BasicBlock, invert_conditional: bool
        ) -> Tuple[ExprList, VarMapping]:
            branch: ExprList = []
            branch_variables = copy(variables)
            # Make typechecker happy. Conditionals had better have a condition
            assert root.conditional
            conditional = to_boolean(convert(root.conditional.code, branch_variables))
            if invert_conditional:
                conditional = z3.Not(conditional)
            branch.append(conditional)
            branch += self._convert_block_tree(child, branch_variables, join)
            return (branch, branch_variables)

        assert root.type == basic_block.Conditional

        true_child, false_child, join = root.children
        code: ExprList = []

        # If any child has a required decendant, convert only that child
        if _is_required(true_child, join):
            code, updated_variables = construct_branch(
                true_child, join, invert_conditional=False
            )
            variables.clear()
            variables.update(updated_variables)
            return code

        if _is_required(false_child, join):
            code, updated_variables = construct_branch(
                false_child, join, invert_conditional=True
            )
            variables.clear()
            variables.update(updated_variables)
            return code

        if root.conditional is None:
            # If the conditional is missing, this branch doesn't matter, and
            # we can skip it.
            return self._convert_block_tree(join, variables, stop)

        if true_child.returns:
            code, updated_variables = construct_branch(
                false_child, join, invert_conditional=True
            )
            variables.clear()
            variables.update(updated_variables)
            code += self._convert_block_tree(join, variables, stop)
            return code

        if false_child.returns:
            code, updated_variables = construct_branch(
                true_child, join, invert_conditional=False
            )
            variables.clear()
            variables.update(updated_variables)
            code += self._convert_block_tree(join, variables, stop)
            return code

        branches = []
        branches.append(construct_branch(true_child, join, invert_conditional=False))
        branches.append(construct_branch(false_child, join, invert_conditional=True))

        branch_exprs, updated_variables = _update_paths(branches)
        variables.clear()
        variables.update(updated_variables)
        combined = map(_combine_conditions, branch_exprs)
        code.append(z3.Or(*combined))
        code += self._convert_block_tree(join, variables, stop)
        return code

    def _convert_code_block(
        self, root: BasicBlock, variables: VarMapping, stop: StopBlock
    ) -> ExprList:
        assert root.type == basic_block.Code
        print("block, code length", root.number, len(root.code))
        code = [convert(c.code, variables) for c in root.code]
        if root.children:
            assert len(root.children) == 1
            code += self._convert_block_tree(root.children[0], variables, stop)
        return code


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
        return z3.And(*conds)
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
