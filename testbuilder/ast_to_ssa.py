import ast
from functools import reduce
from typing import (
    Any,
    List,
    MutableMapping as MMapping,
    Sequence,
    Tuple,
    Type,
    Union,
    cast,
)

from logbook import Logger

import dataclasses

from . import nodetree as n, ssa_basic_blocks as sbb
from .return_checker import contains_return
from .utils import ast_dump
from .variable_manager import VariableManager, VarMapping
from .visitor import GenericVisitor, SimpleVisitor

log = Logger("ast_to_ssa")

StmtList = List[ast.stmt]
MaybeIndex = Union[sbb.BlockTree, sbb.BlockTreeIndex[Any]]


def ast_to_ssa(depth: int, variables: VarMapping, node: ast.AST) -> sbb.Module:
    varmanager = VariableManager(variables)
    t = AstToSSABasicBlocks(depth, varmanager)
    if not isinstance(node, ast.Module):
        assert isinstance(node, ast.stmt)
        node = ast.Module(body=[node])
    res = t.visit(node)
    assert isinstance(res, sbb.Module)
    return res


class AstToSSABasicBlocks(SimpleVisitor[Any]):
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
        classes: MMapping[str, sbb.ClassDef] = {}
        code = []
        for line in node.body:
            if isinstance(line, ast.FunctionDef):
                functions[line.name] = self.visit(line)
            elif isinstance(line, ast.ClassDef):
                classes[line.name] = self.visit(line)
            else:
                code.append(line)
        blocktree = self.body_visit(code)
        return sbb.Module(functions=functions, classes=classes, code=blocktree)

    def visit_ClassDef(self, node: ast.ClassDef) -> sbb.ClassDef:
        last_lineno = last_line(node)
        functions = [
            self.visit(line) for line in node.body if isinstance(line, ast.FunctionDef)
        ]
        first_lineno = node.lineno
        last_lineno = last_line(node)
        return sbb.ClassDef(
            first_line=first_lineno,
            last_line=last_lineno,
            name=node.name,
            variables=[],
            functions=functions,
        )

    def visit_FunctionDef(self, node: ast.FunctionDef) -> sbb.FunctionDef:
        args = [arg.arg for arg in node.args.args]
        defaults = [self.expr_visitor(e) for e in node.args.defaults]
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
            defaults=defaults,
            original=node,
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

    def line_visit(
        self, stmts: StmtList, start_tree: sbb.BlockTreeIndex[Any]
    ) -> MaybeIndex:
        tree: MaybeIndex = start_tree
        for line in stmts:
            tree = self.visit(line, tree)
            if not isinstance(tree, sbb.BlockTreeIndex):
                break

        return tree

    def visit_Stmt(
        self, node: ast.stmt, tree: sbb.BlockTreeIndex[Any]
    ) -> sbb.BlockTreeIndex[Any]:
        assert isinstance(tree, sbb.BlockTreeIndex)
        expr = self.stmt_visitor(node)
        if expr is None:
            return tree
        return self.append_code(tree, expr)

    def visit_If(self, node: ast.If, tree: sbb.BlockTreeIndex[Any]) -> MaybeIndex:
        assert isinstance(tree, sbb.BlockTreeIndex)
        assert tree.target
        condition = self.expr_visitor(node.test)
        paths: List[Tuple[sbb.BlockTreeIndex[Any], VarMapping]] = []
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

    def visit_While(
        self, node: ast.While, tree: sbb.BlockTreeIndex[Any]
    ) -> sbb.BlockTree:
        assert isinstance(tree, sbb.BlockTreeIndex)
        assert tree.target
        paths = []

        def add_block(block: sbb.BlockTreeIndex[Any]) -> None:
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
        self, node: ast.Pass, tree: sbb.BlockTreeIndex[Any]
    ) -> sbb.BlockTreeIndex[Any]:
        return tree

    def visit_Return(
        self, node: ast.Return, tree: sbb.BlockTreeIndex[Any]
    ) -> sbb.BlockTree:
        if node.value is None:
            value = None
        else:
            value = self.expr_visitor(node.value)
        ret = n.Return(line=node.lineno, value=value)
        tree = self.append_code(tree, ret)
        return tree.return_target()

    def visit_Raise(
        self, node: ast.Raise, tree: sbb.BlockTreeIndex[Any]
    ) -> sbb.BlockTree:
        return tree.return_target()

    def append_lines(
        self, tree: sbb.BlockTreeIndex[Any], lines: Sequence[n.stmt]
    ) -> sbb.BlockTreeIndex[Any]:
        for line in lines:
            tree = self.append_code(tree, line)
        return tree

    def append_code(
        self, tree: sbb.BlockTreeIndex[Any], line: n.stmt
    ) -> sbb.BlockTreeIndex[Any]:
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
        self, paths: Sequence[Tuple[sbb.BlockTreeIndex[Any], VarMapping]]
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


class StatementVisitor(GenericVisitor[Any]):
    def __init__(self, variables: VariableManager) -> None:
        self.variables = variables
        self.expr_visitor = AstBuilder(variables)

    def visit_Import(self, node: ast.Import) -> None:
        return None

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        return None

    def visit_Assign(self, node: ast.Assign) -> n.Set:
        expr = self.expr_visitor(node.value)
        target = self.get_target_variable(node.targets[0])
        return n.Set(line=node.lineno, target=target, e=expr)

    def get_target_variable(self, node: ast.expr) -> n.LValue:
        if isinstance(node, ast.Name):
            var: n.Name = self.expr_visitor.visit_Name(node)
            var.set_count = self.variables.get_target(node.id)
            return var
        elif isinstance(node, ast.Attribute):
            val = self.expr_visitor(node.value)
            return n.Attribute(e=val, value=val, attr=node.attr)
        else:
            raise RuntimeError(f"Unknown target type {type(node)}")

    def visit_AugAssign(self, node: ast.AugAssign) -> n.Set:
        value = self.expr_visitor(node.value)
        var = self.expr_visitor(node.target)
        op = self.expr_visitor(node.op)
        target = self.get_target_variable(node.target)
        return n.Set(line=node.lineno, target=target, e=n.BinOp(var, op, value))

    def visit_Expr(self, node: ast.expr) -> n.Expr[Any]:
        expr = self.expr_visitor(node)
        return n.Expr(line=node.lineno, value=expr)

    def generic_visit(self, v: ast.AST, *args: Any, **kwargs: Any) -> Any:
        return self.expr_visitor(v)


class AstBuilder(GenericVisitor[Any]):
    def __init__(self, variables: VariableManager) -> None:
        super().__init__()
        self.variables = variables

    def visit_Num(self, node: ast.Num) -> Union[n.Int, n.Float]:
        if isinstance(node.n, int):
            return n.Int(node.n)
        else:
            return n.Float(node.n)

    def visit_Compare(self, node: ast.Compare) -> n.BinOp:
        left = self.visit(node.left)
        ops = [self.visit(x) for x in node.ops]
        comparators = [self.visit(x) for x in node.comparators]

        lefts = [left] + comparators[:-1]
        rights = comparators
        assert len(lefts) == len(rights) == len(ops)
        binops = []
        for args in zip(lefts, ops, rights):
            binops.append(n.BinOp(*args))

        def all_pairs(l: n.BinOp, r: n.BinOp) -> n.BinOp:
            return n.BinOp(l, n.And(), r)

        res = reduce(all_pairs, binops)
        if __debug__:
            log.debug(f"converting {ast.dump(node)} to {res}")
        return res

    def visit_BoolOp(self, node: ast.BoolOp) -> n.BinOp:
        op = self.visit(node.op)
        value_list = [self.visit(v) for v in node.values]

        def combine(left: n.expr, right: n.expr) -> n.expr:
            return n.BinOp(left, op, right)

        return cast(n.BinOp, reduce(combine, value_list))

    def visit_Name(self, node: ast.Name) -> n.Name:
        idx = self.variables.get(node.id)
        return n.Name(node.id, idx)

    def visit_Attribute(self, node: ast.Attribute) -> n.Attribute:
        value = self.visit(node.value)
        return n.Attribute(e=value, value=value, attr=node.attr)

    def visit_Tuple(self, node: ast.Tuple) -> n.TupleVal:
        return n.TupleVal(elts=[self.visit(v) for v in node.elts])

    def generic_visit(self, v: ast.AST, *args: Any, **kwargs: Any) -> n.Node:
        node = v
        if not isinstance(node, ast.AST):
            return node

        typename = type(node).__name__
        equivalent = getattr(n, typename, None)
        if equivalent is None:
            raise RuntimeError(
                f"Don't know what to do with a {typename}"
                f"({type(node)}); no such attribute exists"
            )
        fields = []
        try:
            dataclass_fields = dataclasses.fields(equivalent)
        except TypeError as err:
            raise TypeError(
                f"Couldn't get fields on {equivalent} of type {type(equivalent)}"
            ) from err
        for field in dataclass_fields:
            if field.name == "line":
                fields.append(getattr(node, "lineno"))
                continue
            value = getattr(node, field.name)
            if isinstance(value, list):
                fields.append([self.visit(v) for v in value])
            else:
                fields.append(self.visit(value))
        return cast(n.Node, equivalent(*fields))


def last_line(node: ast.AST) -> int:
    """
    Return the last line of an AST element
    """
    # `negatives` contains AST elements which should be given negative
    # results, making them lower-priority than any element with a
    # determinable position.

    negatives = [ast.Load, ast.Store, ast.boolop, ast.operator, ast.unaryop, ast.cmpop]

    # `linenos` contains AST elements which have no subparts, and thus
    # must rely on their own `lineno` for their position.
    linenos = {ast.Num, ast.arg, ast.Pass, ast.Name, ast.NameConstant, ast.Str}

    cls: Type[ast.AST]
    for cls in negatives:
        if isinstance(node, cls):
            return -1

    for cls in linenos:
        if isinstance(node, cls):
            return node.lineno

    try:
        return max(last_line(x) for x in ast.iter_child_nodes(node))
    except ValueError as e:
        raise RuntimeError(
            f"Cannot determine last line of a `{type(node).__name__}`"
            f"\nDump:\n{ast_dump(node)}"
        ) from e
