from typing import MutableMapping as MMapping, Optional, Set, TypeVar, cast

from typeassert import assertify

from . import ssa_basic_blocks as sbb
from .visitor import SimpleVisitor

BlockMapping = MMapping[int, sbb.BasicBlock]

B = TypeVar("B", bound=sbb.BasicBlock)


# TODO: Convert to UpdateVisitor
class LineFilterer(SimpleVisitor[sbb.Module]):
    def __init__(self, lines: Set[int]) -> None:
        super().__init__()
        self.lines = lines
        self.min_line = min(lines)
        self.max_line = max(lines)
        self.line_range = range(self.min_line, self.max_line + 1)

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
                    # print(f"Throwing out {func} because {func.lines} > {self.max_line}")
                    continue
            start = min(func.lines)
            end = max(func.lines)
            if start > self.max_line or end < self.min_line:
                # print(
                #     f"Throwing out {func} because {start}>{self.max_line} or {end} < {self.min_line}"
                # )
                continue
            res = self.visit_FunctionDef(func)
            if res is not None:
                code.append(res)
            # else:
            #     print("Throwing out {func} because no lines were kept")

        # Shouldn't have lines from more than one function or basic block
        if len(code) == 0:
            # Check module.code
            blocktree = self.visit_BlockTree(module.code)
            assert isinstance(blocktree, sbb.BlockTree)
            if blocktree.empty():
                raise RuntimeError("No code lines selected")
            return sbb.Request(module=module, code=blocktree)
        elif len(code) > 1:
            raise RuntimeError("Lines from more than one function selected")

        return sbb.Request(module=module, code=code[0])

    def visit_FunctionDef(self, function: sbb.FunctionDef) -> Optional[sbb.FunctionDef]:
        blocktree = self.visit_BlockTree(function.blocks)
        if isinstance(blocktree.start, sbb.ReturnBlock):
            return None
        else:
            start_line = blocktree.start.line
            end_line = blocktree.end.line
            lines = range(start_line, end_line + 1)
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
        # print("visiting blocktree", blocktree)
        sbb.dump_tree(blocktree.end)
        blocks: BlockMapping = {}

        exitnode = self.visit_block(blocktree.end, blocks)
        start_number = blocktree.start.number
        assert start_number in blocks
        start = cast(sbb.StartBlock, blocks[start_number])
        return sbb.BlockTree(start=start, end=exitnode)

    def visit_StartBlock(
        self, block: sbb.StartBlock, blocks: BlockMapping
    ) -> sbb.StartBlock:
        return block

    @assertify
    def visit_block(self, block: B, blocks: BlockMapping) -> B:
        if block.number in blocks:
            return cast(B, blocks[block.number])
        else:
            newblock = cast(B, self.visit(block, blocks))
            blocks[block.number] = newblock
            return newblock

    def visit_Code(self, code: sbb.Code, blocks: BlockMapping) -> Optional[sbb.Code]:
        print("code.parent", code.parent)
        parent = self.visit_block(code.parent, blocks)
        body = [i for i in code.code if i.line in self.lines]
        if body:
            return sbb.Code(
                number=code.number, lines=code.lines, parent=parent, code=body
            )
        else:
            return None


def filter_lines(lines: Set[int], module: sbb.Module) -> sbb.Request:
    print(f"Filtering on lines {lines}")
    filtered = LineFilterer(lines).visit_Module(module)
    print("filtered code", filtered.code)
    return filtered
