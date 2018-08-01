"""
Provides get_expression function to extract a controlling slice of code for the
value at a given line.
"""
import ast
from copy import copy
from functools import reduce
from typing import (
    Any,
    Callable,
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
from .ast_builder import make_ast
from .basic_block import BasicBlock, BlockTree
from .build_tree import RETURNBLOCK, build_tree
from .converter import VAR_START_VALUE, convert, get_variable
from .slicing import Dependency, Variable, take_slice

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


def get_expression(code: ast.AST, line: int, depth: int = 1) -> Optional[Expression]:
    block_tree = build_tree(code)
    dep_tree = take_slice(code, line)
    print("dep_tree", dep_tree, "end")
    if not dep_tree:
        return None
    tree = block_tree.inflate(dep_tree)
    from .test_utils import show_dot

    print("tree", tree)
    # show_dot(tree.entrance.dot())
    variables = dep_tree.get_slice_variables()
    eb = ExpressionBuilder(depth)
    return eb.get_expression(variables, tree)


class ExpressionBuilder:
    def __init__(self, depth: int) -> None:
        self.depth = depth

    def get_expression(
        self, variables: Iterable[Variable], flowgraph: BlockTree
    ) -> Expression:
        expr_list: ExprList = self.convert_tree(flowgraph, variables)
        return _combine_conditions(expr_list)

    def convert_tree(self, tree: BlockTree, variables: Iterable[Variable]) -> ExprList:
        # Sets variables to the default value, to treat them as having been defined
        # before the blocks begin. Mostly important for handling function
        # arguments.
        mutation_counts = {v.code: VAR_START_VALUE for v in variables}
        assert tree.target
        print("target", tree.target, tree.target.number)
        return self._convert_target_tree(tree.target, None, mutation_counts, None)

    def _convert_target_tree(
        self,
        root: BasicBlock,
        coming_from: Optional[BasicBlock],
        variables: VarMapping,
        stop: StopBlock = None,
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

        print("root type", root.type, root.number)
        assert root.number != RETURNBLOCK
        print("Not return block")
        if root is stop:
            print("stopping")
            return []

        if root.type == basic_block.Loop:
            return self._convert_target_loop(root, coming_from, variables, stop)
            assert root.type != basic_block.Loop
        elif root.type == basic_block.Conditional:
            return self._convert_target_conditional(root, variables, stop)
        elif root.type == basic_block.Code or root.type == basic_block.StartConditional:
            return self._convert_target_code_block(root, variables, stop)
        raise RuntimeError(f"Unknown block type: {root.type}")

    def _handle_parents(
        self,
        parent: BasicBlock,
        root: BasicBlock,
        variables: VarMapping,
        stop: StopBlock,
    ) -> ExprList:
        code = self._convert_target_tree(parent, root, variables, stop)
        if (
            parent.type == basic_block.StartConditional
            or parent.type == basic_block.Loop
        ):
            if parent.conditional:
                invert_conditional = root is parent.children[1]
                conditional = to_boolean(
                    self._convert(parent.conditional.code, variables)
                )
                if invert_conditional:
                    print("Inverting conditional on", root)
                    conditional = bool_not(conditional)
                code.append(conditional)
        print("parent code", code)
        return code

    def _convert_target_code_block(
        self, root: BasicBlock, variables: VarMapping, stop: StopBlock
    ) -> ExprList:
        assert (
            root.type == basic_block.Code or root.type == basic_block.StartConditional
        )
        code: ExprList
        if root.parents:
            print("parents exist")
            assert len(root.parents) == 1
            parent = root.parents[0]
            assert parent
            code = self._handle_parents(parent, root, variables, stop)
        else:
            code = []

        code += [self._convert(c.code, variables) for c in root.code]
        print("code block code", code)
        return code

    def _convert_target_loop(
        self,
        root: BasicBlock,
        coming_from: Optional[BasicBlock],
        variables: VarMapping,
        stop: StopBlock,
    ) -> ExprList:
        def construct_path(
            path: ExprList, path_vars: VarMapping
        ) -> Tuple[ExprList, VarMapping]:
            path = copy(path)
            path_vars = copy(path_vars)
            return (path, path_vars)

        assert root.type == basic_block.Loop

        body, bypass = root.parents
        assert len(root.children) > 0
        body_end = root.children[0]
        assert body_end is not None
        assert bypass is not None
        if body is None or body_end == coming_from:
            # If we want to get into the body, there is no need to run it again
            depth = 0
        else:
            depth = self.depth

        code = self._handle_parents(bypass, root, variables, stop)

        if root.conditional is None:
            print("No conditional on root")
            print("root", root.number)
            # If the conditional is missing, this loop doesn't matter, and we
            # can skip it.
            return code

        paths = [construct_path([], variables)]

        loops: ExprList = []
        for _i in range(depth):
            assert body is not None
            loops += self._convert_target_tree(body, root, variables, root)
            paths.append(construct_path(loops, variables))

        print("Paths through loop:", paths)
        updated_conditions, updated_variables = _update_paths(paths)
        variables.clear()
        variables.update(updated_variables)

        if any(len(c) == 0 for c in updated_conditions):
            print("updated_conditions", updated_conditions)
        conditions = [
            _combine_conditions(code) for code in updated_conditions if len(code) > 0
        ]
        if len(conditions) > 1:
            code += [bool_or(*conditions)]
        elif len(conditions) == 1:
            code += [conditions[0]]

        return code

    def _convert_target_conditional(
        self, root: BasicBlock, variables: VarMapping, stop: StopBlock
    ) -> ExprList:
        def construct_branch(
            parent: BasicBlock, join: BasicBlock, invert_conditional: bool
        ) -> Tuple[ExprList, VarMapping]:
            branch_variables = copy(variables)
            branch: ExprList = []
            branch += self._convert_target_tree(parent, root, branch_variables, join)
            print("branch code", branch)
            return (branch, branch_variables)

        assert root.type == basic_block.Conditional

        print("checking parent length")
        assert len(root.parents) == 3
        true_branch, false_branch, join = root.parents
        assert join is not None
        assert len(join.parents) == 1
        if join.parents[0] is not None:
            code = self._handle_parents(join.parents[0], join, variables, stop)
        else:
            code = []

        if join.conditional is None:
            print("No conditional on join")
            print("join", join.number)
            # If the conditional is missing, this branch doesn't matter, and
            # we can skip it.
            return code

        branches = []
        if true_branch:
            branches.append(
                construct_branch(true_branch, join, invert_conditional=False)
            )
        if false_branch:
            branches.append(
                construct_branch(false_branch, join, invert_conditional=True)
            )
        print("branches", branches)

        branch_exprs, updated_variables = _update_paths(branches)
        variables.clear()
        variables.update(updated_variables)
        combined = map(_combine_conditions, branch_exprs)
        code.append(bool_or(*combined))
        code += [self._convert(s.code, variables) for s in root.code]
        return code

    def _convert(self, code: ast.AST, variables: MMapping[str, int]) -> Expression:
        tree = make_ast(code, variables)
        result = convert(tree)
        return result


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
