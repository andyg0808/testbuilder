import ast
from copy import copy
from functools import singledispatch
from typing import Callable, List, MutableMapping as MMapping, Optional, Set, cast

from . import nodetree as n, ssa_basic_blocks as sbb
from .ast_builder import AstBuilder
from .expression_builder import VarMapping
from .slicing import Dependency
from .utils import crash

StmtList = List[ast.stmt]


class AstToSSABasicBlocks(AstBuilder):
    def __init__(self, lines: Set[int], variables: VarMapping) -> None:
        self.lines = lines
        self.block_id = 0
        super().__init__(variables)
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
        blocktree = self.visit_body(code)
        return sbb.Module(functions, blocktree)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> sbb.FunctionDef:
        args = [arg.arg for arg in node.args.args]
        blocktree = self.visit_body(node.body)
        lines = range(blocktree.start.line, blocktree.end.line + 1)
        return sbb.FunctionDef(lines, node.name, args, blocktree)

    def visit_body(self, code: List[ast.stmt]) -> sbb.BlockTree:
        if len(code) > 0:
            lineno = code[0].lineno
        else:
            lineno = 0
        start_block = sbb.StartBlock(number=self.next_id(), line=lineno)
        ret_block = sbb.ReturnBlock(number=self.next_id())
        block: sbb.BasicBlock = start_block
        for line in code:
            print("looking at line", line)
            block = self.visit_stmt(ret_block, block, line)

        ret_block.append(block)
        return sbb.BlockTree(start=start_block, end=ret_block)

    def visit_stmt(
        self, ret_block: sbb.BasicBlock, cur_block: sbb.BasicBlock, line: ast.stmt
    ) -> sbb.BasicBlock:
        if not isinstance(cur_block, sbb.Code):
            if isinstance(cur_block, sbb.Positioned):
                cur_block.lines = range(cur_block.lines, line.lineno)
            cur_block = sbb.Code(
                number=self.next_id(),
                lines=range(line.lineno, line.lineno + 1),
                parent=cur_block,
                code=[self.visit(line)],
            )
        else:
            cur_block.append(self.visit(line))
        return cur_block



def ast_to_ssa(lines: Set[int], variables: VarMapping, node: ast.AST) -> sbb.Module:
    # print("input type", type(node))
    t = AstToSSABasicBlocks(lines, variables)
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
