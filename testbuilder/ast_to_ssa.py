import ast
from functools import reduce, singledispatch
from typing import (
    Any,
    List,
    MutableMapping as MMapping,
    Optional,
    Sequence,
    Tuple,
    Type,
    Union,
    cast,
)

import dataclasses

from . import nodetree as n, ssa_basic_blocks as sbb
from .return_checker import contains_return
from .variable_manager import VariableManager, VarMapping
from .visitor import GenericVisitor, SimpleVisitor

StmtList = List[ast.stmt]
MaybeIndex = Union[sbb.BlockTree, sbb.BlockTreeIndex]


def ast_to_ssa(depth: int, variables: VarMapping, node: ast.AST) -> sbb.Module:
    varmanager = VariableManager(variables)
    t = AstToSSABasicBlocks(depth, varmanager)
    if not isinstance(node, ast.Module):
        assert isinstance(node, ast.stmt)
        node = ast.Module(body=[node])
    res = t.visit(node)
    assert isinstance(res, sbb.Module)
    return res


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
        self.variables.push()
        self.variables.add(args)
        blocktree = self.body_visit(node.body)
        self.variables.pop()
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
        blocktree: sbb.BlockTreeIndex[sbb.StartBlock] = sbb.BlockTreeIndex.construct(
            start=start_block, end=return_block
        )
        final = self.line_visit(stmts, blocktree)
        if isinstance(final, sbb.BlockTreeIndex):
            return final.return_target()
        else:
            return final

    def line_visit(self, stmts: StmtList, start_tree: sbb.BlockTreeIndex) -> MaybeIndex:
        tree: MaybeIndex = start_tree
        for line in stmts:
            tree = self.visit(line, tree)
            if not isinstance(tree, sbb.BlockTreeIndex):
                break

        return tree

    def visit_Stmt(
        self, node: ast.stmt, tree: sbb.BlockTreeIndex
    ) -> sbb.BlockTreeIndex:
        assert isinstance(tree, sbb.BlockTreeIndex)
        expr = self.stmt_visitor(node)
        return self.append_code(tree, expr)

    def visit_If(self, node: ast.If, tree: sbb.BlockTreeIndex) -> MaybeIndex:
        assert isinstance(tree, sbb.BlockTreeIndex)
        assert tree.target
        condition = self.expr_visitor(node.test)
        paths: List[Tuple[sbb.BlockTreeIndex, VarMapping]] = []
        returns: List[sbb.BlockTree] = []

        def add_block(block: MaybeIndex) -> None:
            if isinstance(block, sbb.BlockTreeIndex):
                paths.append((block, self.variables.mapping()))
            else:
                returns.append(block)

        if contains_return(node.orelse):
            true_branch: Type[sbb.TrueBranch] = sbb.ForcedTrueBranch
        else:
            true_branch = sbb.TrueBranch
        true_block = tree.map_target(
            lambda parent: true_branch(
                number=self.next_id(),
                conditional=condition,
                parent=parent,
                line=node.lineno,
            )
        )
        if contains_return(node.body):
            false_branch: Type[sbb.FalseBranch] = sbb.ForcedFalseBranch
        else:
            false_branch = sbb.FalseBranch
        false_block = tree.map_target(
            lambda parent: false_branch(
                number=self.next_id(),
                conditional=condition,
                parent=parent,
                line=node.lineno,
            )
        )

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

        last_line = max(sbb.last_line(b) for b in blocks)
        return tree.map_targets(
            lambda parent, true, false: sbb.Conditional(
                number=self.next_id(),
                first_line=node.lineno,
                last_line=last_line,
                parent=parent,
                true_branch=true,
                false_branch=false,
            ),
            *blocks,
        )

    def visit_While(self, node: ast.While, tree: sbb.BlockTreeIndex) -> sbb.BlockTree:
        assert isinstance(tree, sbb.BlockTreeIndex)
        assert tree.target
        paths = []

        def add_block(block: sbb.BlockTreeIndex) -> None:
            paths.append((block, self.variables.mapping()))

        bypass = tree.map_target(
            lambda parent: sbb.Code(
                number=self.next_id(),
                first_line=n.AddedLine,
                last_line=n.AddedLine,
                parent=parent,
                code=[],
            )
        )
        add_block(bypass)
        for depth in range(1, self.depth + 1):
            indexed_branch = tree
            self.variables.push()
            for _i in range(depth):
                condition = self.expr_visitor(node.test)
                indexed_branch = indexed_branch.map_target(
                    lambda parent: sbb.TrueBranch(
                        number=self.next_id(),
                        conditional=condition,
                        parent=parent,
                        line=node.lineno,
                    )
                )
                new_branch = self.line_visit(node.body, indexed_branch)
                if isinstance(new_branch, sbb.BlockTreeIndex):
                    indexed_branch = new_branch
                else:
                    # We must have returned. We don't have an active
                    # end to attach to.
                    break
            if isinstance(new_branch, sbb.BlockTreeIndex):
                add_block(new_branch)
                self.variables.pop()
            else:
                self.variables.pop()
                break

        loops, variables = self._update_paths(paths)
        self.variables.update(variables)

        last_line = sbb.last_line(new_branch)

        loop = tree.map_targets(
            lambda parent, *loops: sbb.Loop(
                number=self.next_id(),
                first_line=node.lineno,
                last_line=last_line,
                parent=parent,
                loops=cast(List[sbb.BasicBlock], list(loops)),
            ),
            *loops,
        )
        condition = self.expr_visitor(node.test)
        child = loop.map_target(
            lambda parent: sbb.WhileFalseBranch(
                number=self.next_id(),
                conditional=condition,
                parent=parent,
                line=node.lineno,
                controlled_line=last_line + 1,
            )
        )
        if type(new_branch) == sbb.BlockTree:
            child = child.unify_return(new_branch)

        # return tree.set_target(child)
        return child

    def visit_Pass(
        self, node: ast.Pass, tree: sbb.BlockTreeIndex
    ) -> sbb.BlockTreeIndex:
        return tree

    def visit_Return(self, node: ast.Return, tree: sbb.BlockTreeIndex) -> sbb.BlockTree:
        if node.value is None:
            value = None
        else:
            value = self.expr_visitor(node.value)
        ret = n.Return(line=node.lineno, value=value)
        tree = self.append_code(tree, ret)
        return tree.return_target()

    def append_lines(
        self, tree: sbb.BlockTreeIndex, lines: Sequence[n.stmt]
    ) -> sbb.BlockTreeIndex:
        for line in lines:
            tree = self.append_code(tree, line)
        return tree

    def append_code(self, tree: sbb.BlockTreeIndex, line: n.stmt) -> sbb.BlockTreeIndex:
        def append_to_block(cur_block: sbb.BasicBlock) -> sbb.Code:
            if not isinstance(cur_block, sbb.Code):
                return sbb.Code(
                    number=self.next_id(),
                    first_line=line.line,
                    last_line=line.line,
                    parent=cur_block,
                    code=[line],
                )
            else:
                cur_block.append(line)
                if line.line != n.AddedLine:
                    # Don't update line numbers to be negative. This
                    # eliminates later need to sort through the lines in
                    # the code block to find the actual end line.
                    cur_block.last_line = line.line
                return cur_block

        return tree.map_target(append_to_block)

    def _update_paths(
        self, paths: Sequence[Tuple[sbb.BlockTreeIndex, VarMapping]]
    ) -> Tuple[List[sbb.BlockTreeIndex[sbb.Code]], VarMapping]:
        variables, edit_lists = unify_all_variables([p[1] for p in paths])
        updated_conditions: List[sbb.BlockTreeIndex[sbb.Code]] = []
        for pathinfo, edit_list in zip(paths, edit_lists):
            path = pathinfo[0]
            newblock = self.append_lines(path, edit_list)
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

    def generic_visit(self, v: ast.AST, *args: Any, **kwargs: Any) -> Any:
        return self.expr_visitor(v)


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

    def generic_visit(self, v: ast.AST, *args: Any, **kwargs: Any) -> n.Node:
        node = v
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
