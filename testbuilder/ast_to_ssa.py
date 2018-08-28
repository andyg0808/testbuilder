import ast
from functools import reduce, singledispatch
from typing import (
    Any,
    Callable,
    List,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
    cast,
)

import dataclasses
import z3
from typeassert import assertify

from . import nodetree as n, ssa_basic_blocks as sbb
from .converter import get_variable
from .expression_builder import VarMapping
from .slicing import Dependency
from .utils import crash
from .variable_manager import VariableManager
from .visitor import GenericVisitor, SimpleVisitor

StmtList = List[ast.stmt]


class AstToSSABasicBlocks(SimpleVisitor):
    def __init__(self, depth: int, variables: VariableManager) -> None:
        self.block_id = 0
        self.depth = depth
        self.variables = variables
        self.stmt_visitor = StatementVisitor(variables)
        self.expr_visitor = AstBuilder(variables)
        assert self.variables is not None

    def next_id(self) -> int:
        self.block_id += 1
        return self.block_id

    def visit_Module(self, node: ast.Module) -> sbb.Module:
        functions: MMapping[str, sbb.FunctionDef] = {}
        code = []
        for line in node.body:
            if isinstance(line, ast.FunctionDef):
                functions[line.name] = self.visit(line)
            else:
                code.append(line)
        blocktree = self.body_visit(code)
        return sbb.Module(functions, blocktree)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> sbb.FunctionDef:
        args = [arg.arg for arg in node.args.args]
        blocktree = self.body_visit(node.body)
        print(blocktree)
        return sbb.FunctionDef(
            first_line=blocktree.start.line,
            last_line=blocktree.end.line,
            name=node.name,
            args=args,
            blocks=blocktree,
        )

    def body_visit(self, stmts: StmtList) -> sbb.BlockTree:
        if stmts:
            lineno = stmts[0].lineno
        else:
            lineno = 0
        start_block = sbb.StartBlock(number=self.next_id(), line=lineno)
        return_block = sbb.ReturnBlock(number=self.next_id())
        blocktree = sbb.BlockTreeIndex(
            start=start_block, end=return_block, target=start_block
        )
        final = self.line_visit(stmts, blocktree)
        if isinstance(final, sbb.BlockTreeIndex):
            return final.return_target()
        else:
            return final

    def line_visit(
        self, stmts: StmtList, tree: sbb.BlockTreeIndex
    ) -> sbb.BlockTreeIndex:
        for line in stmts:
            tree = self.visit(line, tree)

        return tree

    def visit_Stmt(
        self, node: ast.stmt, tree: sbb.BlockTreeIndex
    ) -> sbb.BlockTreeIndex:
        assert isinstance(tree, sbb.BlockTreeIndex)
        expr = self.stmt_visitor(node)
        return self.append_code(tree, expr)

    def visit_If(self, node: ast.If, tree: sbb.BlockTreeIndex) -> sbb.BlockTreeIndex:
        assert isinstance(tree, sbb.BlockTreeIndex)
        assert tree.target
        parent = tree.target
        condition = self.expr_visitor(node.test)
        paths = []
        returns = []

        def add_block(block: sbb.BlockTreeIndex) -> None:
            if type(block) == sbb.BlockTree:
                returns.append(block)
            else:
                paths.append((block, self.variables.mapping()))

        true_branch = sbb.TrueBranch(
            number=self.next_id(),
            conditional=condition,
            parent=parent,
            line=node.lineno,
        )
        false_branch = sbb.FalseBranch(
            number=self.next_id(),
            conditional=condition,
            parent=parent,
            line=node.lineno,
        )
        true_block = tree.set_target(true_branch)
        false_block = tree.set_target(false_branch)

        self.variables.push()
        add_block(self.line_visit(node.body, true_block))
        self.variables.refresh()
        add_block(self.line_visit(node.orelse, false_block))
        self.variables.pop()

        blocks, variables = self._update_paths(paths)
        self.variables.update(variables)
        if len(blocks) == 1:
            return blocks[0].unify_return(returns[0])
        if len(blocks) == 0:
            return returns[0].unify_return(returns[1])

        true_block, false_block = blocks
        last_line = max(sbb.last_line(true_block), sbb.last_line(false_block))
        return tree.set_target(
            sbb.Conditional(
                number=self.next_id(),
                first_line=node.lineno,
                last_line=last_line,
                parent=parent,
                true_branch=true_block.target,
                false_branch=false_block.target,
            )
        )

    def visit_While(self, node: ast.While, tree: sbb.BlockTreeIndex) -> sbb.BlockTree:
        assert isinstance(tree, sbb.BlockTreeIndex)
        assert tree.target
        parent = tree.target
        paths = []

        def add_block(block: sbb.BlockTreeIndex) -> None:
            paths.append((block, self.variables.mapping()))

        bypass = tree.set_target(
            sbb.Code(
                number=self.next_id(),
                first_line=n.AddedLine,
                last_line=n.AddedLine,
                parent=parent,
                code=[],
            )
        )
        add_block(bypass)
        for depth in range(1, self.depth + 1):
            body_branch = tree
            self.variables.push()
            for _i in range(depth):
                condition = self.expr_visitor(node.test)
                body_branch = body_branch.set_target(
                    sbb.TrueBranch(
                        number=self.next_id(),
                        conditional=condition,
                        parent=body_branch.target,
                        line=node.lineno,
                    )
                )
                body_branch = self.line_visit(node.body, body_branch)
                if type(body_branch) == sbb.BlockTree:
                    # We must have returned. We don't have an active
                    # end to attach to.
                    break
            if type(body_branch) == sbb.BlockTree:
                self.variables.pop()
                break
            else:
                add_block(body_branch)
                self.variables.pop()

        loops, variables = self._update_paths(paths)
        self.variables.update(variables)

        last_line = paths[0][0].target.last_line

        loop = sbb.Loop(
            number=self.next_id(),
            first_line=node.lineno,
            last_line=last_line,
            parent=parent,
            loops=[loop.target for loop in loops],
        )
        condition = self.expr_visitor(node.test)
        child = sbb.FalseBranch(
            number=self.next_id(), conditional=condition, parent=loop, line=node.lineno
        )
        if type(body_branch) == sbb.BlockTree:
            tree = tree.unify_return(body_branch)

        return tree.set_target(child)

    def visit_Pass(
        self, node: ast.Pass, tree: sbb.BlockTreeIndex
    ) -> sbb.BlockTreeIndex:
        return tree


    def append_lines(
        self, tree: sbb.BlockTreeIndex, lines: Sequence[n.stmt]
    ) -> sbb.BlockTreeIndex:
        for line in lines:
            tree = self.append_code(tree, line)
        return tree

    def append_code(self, tree: sbb.BlockTreeIndex, line: n.stmt) -> sbb.BlockTreeIndex:
        cur_block = tree.target
        if not isinstance(cur_block, sbb.Code):
            if isinstance(cur_block, sbb.Positioned):
                cur_block.last_line = line.line - 1
            cur_block = sbb.Code(
                number=self.next_id(),
                first_line=line.line,
                last_line=line.line,
                parent=cur_block,
                code=[line],
            )
            return sbb.BlockTreeIndex(start=tree.start, end=tree.end, target=cur_block)
        else:
            cur_block.append(line)
            if line.line != n.AddedLine:
                # Don't update line numbers to be negative. This
                # eliminates later need to sort through the lines in
                # the code block to find the actual end line.
                cur_block.last_line = line.line
            return tree

    def _update_paths(
        self, paths: List[Tuple[sbb.BlockTreeIndex, VarMapping]]
    ) -> Tuple[List[sbb.BlockTreeIndex[sbb.Code]], VarMapping]:
        variables, edit_lists = unify_all_variables([p[1] for p in paths])
        updated_conditions: List[sbb.BlockTreeIndex[sbb.Code]] = []
        for path, edit_list in zip(paths, edit_lists):
            newblock = self.append_lines(path[0], edit_list)
            updated_conditions.append(newblock)
        return (updated_conditions, variables)


SetList = List[n.PhiSet]


def unify_all_variables(
    variable_lists: Sequence[VarMapping]
) -> Tuple[VarMapping, List[SetList]]:
    """
        Args:
            variable_lists: A list of mappings from variable names to
            use counts.

        Returns:
            A tuple of a new variable mapping and a list of additional
            expressions to add to each of the expression lists
            associated with the variable_lists passed in. The list of
            additional expressions is in the same order as the lists
            in variable_lists
        """
    if not variable_lists:
        return ({}, [])
    available_variables = (x.keys() for x in variable_lists)
    keys = reduce(lambda x, y: x | y, available_variables)
    renamings: List[SetList] = [[] for i in variable_lists]
    variables = {}
    first = variable_lists[0]
    for key in sorted(keys):
        # Handle the special case where all the variable lists have
        # the same value. We don't want to waste time on fancy things
        # then.
        if key in first:
            expected = first[key]
            if all(lambda x: key in x and x[key] == expected for x in variable_lists):
                variables[key] = expected
                next
        max_value = max(x.get(key, 0) for x in variable_lists)
        dest = n.Name(id=key, set_count=max_value)
        for var_list, var_renaming in zip(variable_lists, renamings):
            if key in var_list and var_list[key] != max_value:
                source = n.Name(id=key, set_count=var_list[key])
                var_renaming.append(n.PhiSet(line=n.AddedLine, target=dest, e=source))
        variables[key] = max_value

    return (variables, renamings)


# def merge_block_trees(
#     self,
#     left: sbb.BlockTree,
#     right: sbb.BlockTree,
#     joint: Callable[[sbb.BasicBlock, sbb.BasicBlock], sbb.BasicBlock],
# ) -> sbb.BlockTree:
#     assert (
#         left.start is right.start
#     ), "Both BlockTrees need to originate from the same start point"
#     assert left.target, f"Left {left} does not have target set"
#     assert right.target, f"Right {right} does not have target set"
#     return sbb.BlockTree(
#         start=left.start,
#         target=joint(left.target, right.target),
#         end=sbb.ReturnBlock(
#             number=self.next_id(), parents=left.end.parents + right.end.parents
#         ),
#     )


def ast_to_ssa(depth: int, variables: VarMapping, node: ast.Module) -> sbb.Module:
    # print("input type", type(node))
    varmanager = VariableManager(variables)
    t = AstToSSABasicBlocks(depth, varmanager)
    assert isinstance(node, ast.Module)
    res = t.visit(node)
    assert isinstance(res, sbb.Module)
    # print("ast_to_ssa result", res)
    return res


@singledispatch
def find_start_line(block: object) -> Optional[int]:
    return None


@find_start_line.register(sbb.Parented)
def find_parented_start(block: sbb.Parented) -> int:
    parent_line = find_start_line(block.parent)
    if parent_line is None:
        return find_block_start(block)
    else:
        return parent_line


@singledispatch
def find_block_start(block: sbb.Parented) -> int:
    raise RuntimeError(f"Unimplemented for type {type(block)}")


# @find_block_start.regsiter(sbb.Code)
# def find_code_start(block: sbb.Code) ->


class StatementVisitor(GenericVisitor):
    def __init__(self, variables: VariableManager) -> None:
        self.variables = variables
        self.expr_visitor = AstBuilder(variables)

    def visit_Assign(self, node: ast.Assign) -> n.Set:
        expr = self.expr_visitor(node.value)
        target = self.get_target_variable(node.targets[0])
        return n.Set(line=node.lineno, target=target, e=expr)

    def get_target_variable(self, node: ast.expr) -> n.Name:
        if isinstance(node, ast.Name):
            var: n.Name = self.expr_visitor.visit_Name(node)
            var.set_count = self.variables.get_target(node.id)
            return var
        else:
            raise RuntimeError("Unknown target type")

    def visit_AugAssign(self, node: ast.AugAssign) -> n.Set:
        value = self.expr_visitor(node.value)
        var = self.expr_visitor(node.target)
        op = self.expr_visitor(node.op)
        target = self.get_target_variable(node.target)
        return n.Set(line=node.lineno, target=target, e=n.BinOp(var, op, value))

    def visit_Expr(self, node: ast.expr) -> n.Expr:
        expr = self.expr_visitor(node)
        return n.Expr(line=node.lineno, value=expr)

    def generic_visit(self, node: ast.AST, *args: Any) -> Any:
        return self.expr_visitor(node)


class AstBuilder(GenericVisitor):
    def __init__(self, variables: VariableManager) -> None:
        super().__init__()
        self.variables = variables

    def visit_Num(self, node: ast.Num) -> Union[n.Int, n.Float]:
        if int(node.n) == node.n:
            return n.Int(int(node.n))
        else:
            return n.Float(node.n)

    def visit_Compare(self, node: ast.Compare) -> n.BinOp:
        left = self.visit(node.left)
        ops = map(self.visit, node.ops)
        comparators = map(self.visit, node.comparators)

        def combine(left: n.expr, zipped: Tuple[n.expr, n.expr]) -> n.expr:
            op, right = zipped
            return n.BinOp(left, cast(n.Operator, op), right)

        return cast(n.BinOp, reduce(combine, zip(ops, comparators), left))

    def visit_BoolOp(self, node: ast.BoolOp) -> n.BinOp:
        op = self.visit(node.op)
        value_list = [self.visit(v) for v in node.values]

        def combine(left: n.expr, right: n.expr) -> n.expr:
            return n.BinOp(left, op, right)

        return cast(n.BinOp, reduce(combine, value_list))

    def visit_Name(self, node: ast.Name) -> n.Name:
        idx = self.variables.get(node.id)
        return n.Name(node.id, idx)

    def generic_visit(self, node: ast.AST, *args: Any) -> n.Node:
        # print(f"visiting generically to {node}")
        if not isinstance(node, ast.AST):
            return node

        typename = type(node).__name__
        # print("typename", typename)
        equivalent = getattr(n, typename, None)
        if equivalent is None:
            raise RuntimeError(
                f"Don't know what to do with a {typename}"
                f"({type(node)}); no such attribute exists"
            )
        fields = []
        for field in dataclasses.fields(equivalent):
            if field.name == "line":
                fields.append(getattr(node, "lineno"))
                continue
            value = getattr(node, field.name)
            if isinstance(value, list):
                fields.append([self.visit(v) for v in value])
            else:
                fields.append(self.visit(value))
        return cast(n.Node, equivalent(*fields))
