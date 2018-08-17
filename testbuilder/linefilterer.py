from typing import MutableMapping as MMapping, Optional, Set

from typeassert import assertify

from . import ssa_basic_blocks as sbb
from .visitor import SimpleVisitor

BlockMapping = MMapping[int, sbb.BasicBlock]


class LineFilterer(SimpleVisitor[sbb.Module]):
    def __init__(self, lines: Set[int]) -> None:
        super().__init__()
        self.lines = lines
        self.min_line = min(lines)
        self.max_line = max(lines)
        self.line_range = range(self.min_line, self.max_line)

    def visit_Module(self, module: sbb.Module) -> sbb.Request:
        code = []
        for func in module.functions.values():
            # These are the two cases where we can be sure that the
            # function is entirely outside of the line range. In
            # either of these cases, we will ignore the
            # function. Otherwise, we need to see if there's code to
            # include from it.
            if isinstance(func.lines, int):
                if func.lines > self.max_line:
                    continue
            else:
                start = min(func.lines)
                end = max(func.lines)
                if start > self.max_line or end < self.min_line:
                    continue
            res = self.visit(func)
            if res is not None:
                code.append(res)
        # Shouldn't have lines from more than one function or basic block
        if len(code) == 0:
            raise RuntimeError("No code lines selected")
        elif len(code) > 1:
            raise RuntimeError("Lines from more than one function selected")

        return sbb.Request(module, code[0])

    def visit_FunctionDef(self, function: sbb.FunctionDef) -> Optional[sbb.FunctionDef]:
        blocktree = self.visit(function.blocks)
        if isinstance(blocktree.start, sbb.ReturnBlock):
            return None
        else:
            start_line = blocktree.start.line
            end_line = blocktree.end.line
            lines = range(start_line, end_line)
            return sbb.FunctionDef(
                lines=lines, name=function.name, args=function.args, blocks=blocktree
            )

    def visit_ReturnBlock(
        self, block: sbb.ReturnBlock, blocks: BlockMapping
    ) -> sbb.ReturnBlock:
        @assertify
        def parent_map(parent: sbb.BasicBlock) -> Optional[sbb.BasicBlock]:
            assert isinstance(parent, sbb.BasicBlock)
            return self.visit_block(parent, blocks)

        parents = list(filter(None, map(parent_map, block.parents)))
        return sbb.ReturnBlock(number=block.number, parents=parents)

    def visit_BlockTree(self, blocktree: sbb.BlockTree) -> sbb.BlockTree:
        print("visiting blocktree", blocktree)
        sbb.dump_tree(blocktree.end)
        blocks: BlockMapping = {}

        exitnode = self.visit_block(blocktree.end, blocks)
        if len(exitnode.parents) == 0:
            return sbb.BlockTree(start=exitnode, end=exitnode)
        else:
            start_number = blocktree.start.number
            start = blocks[start_number]
            return sbb.BlockTree(start=start, end=exitnode)

    def visit_StartBlock(
        self, block: sbb.StartBlock, blocks: BlockMapping
    ) -> sbb.StartBlock:
        return block

    @assertify
    def visit_block(
        self, block: sbb.BasicBlock, blocks: BlockMapping
    ) -> Optional[sbb.BasicBlock]:
        if block.number in blocks:
            return blocks[block.number]
        else:
            newblock = self.visit(block, blocks)
            blocks[block.number] = newblock
            return newblock

    def visit_Code(self, code: sbb.Code, blocks: BlockMapping) -> Optional[sbb.Code]:
        print("code.parent", code.parent)
        parent = self.visit_block(code.parent, blocks)
        body = [i for i in code.code if i.line in self.lines]
        if body:
            return sbb.Code(code.number, code.lines, parent, code)
        else:
            return None


def filter_lines(lines: Set[int], module: sbb.Module) -> sbb.Module:
    print(f"Filtering on lines {lines}")
    return LineFilterer(lines).visit(module)
