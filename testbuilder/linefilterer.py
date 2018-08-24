from typing import MutableMapping as MMapping, Optional, Set, TypeVar, cast

from logbook import debug, info, notice

from typeassert import assertify

from . import ssa_basic_blocks as sbb
from .visitor import SimpleVisitor, UpdateVisitor

BlockMapping = MMapping[int, sbb.BasicBlock]

B = TypeVar("B", bound=sbb.BasicBlock)


# TODO: Convert to UpdateVisitor
class LineFilterer(UpdateVisitor):
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
                    notice(
                        f"Throwing out {func} because {func.lines} > "
                        f"{self.max_line}"
                    )
                    continue
            start = min(func.lines)
            end = max(func.lines)
            if start > self.max_line or end < self.min_line:
                notice(
                    f"Throwing out {func} because {start}>{self.max_line}"
                    f" or {end} < {self.min_line}"
                )
                continue
            res = self.visit_FunctionDef(func)
            if res is not None:
                code.append(res)
            else:
                notice("Throwing out {func} because no lines were kept")

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
            return sbb.FunctionDef(
                first_line=blocktree.start.line,
                last_line=blocktree.end.line,
                name=function.name,
                args=function.args,
                blocks=blocktree,
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

    # def visit_BlockTreeIndex(self, blocktree: sbb.BlockTreeIndex) -> sbb.BlockTreeIndex:
    #     blocks: BlockMapping = {}

    #     exitnode = self.visit_block(blocktree.end, blocks)
    #     # target_number = blocktree.target.number
    #     # assert target_number in blocks
    #     # target = blocks[target_number]
    #     return sbb.BlockTreeIndex(start=blocktree.start, end=exitnode, target=target)

    def visit_BlockTree(self, blocktree: sbb.BlockTree) -> sbb.BlockTree:
        blocks: BlockMapping = {}
        exitnode = self.visit_block(blocktree.end, blocks)
        return sbb.BlockTree(start=blocktree.start, end=exitnode)

    def visit_StartBlock(
        self, block: sbb.StartBlock, blocks: BlockMapping
    ) -> sbb.StartBlock:
        blocks[block.number] = block
        return block

    @assertify
    def visit_block(self, block: B, blocks: BlockMapping) -> B:
        if block.number in blocks:
            return cast(B, blocks[block.number])
        else:
            newblock = self.visit(block, blocks)
            blocks[block.number] = newblock
            return newblock

    def visit_Code(self, code: sbb.Code, blocks: BlockMapping) -> sbb.BasicBlock:
        print("code.parent", code.parent)
        parent = self.visit_block(code.parent, blocks)
        body = [i for i in code.code if i.line in self.lines]
        if body:
            return sbb.Code(
                number=code.number,
                first_line=code.first_line,
                last_line=code.last_line,
                parent=parent,
                code=body,
            )
        else:
            return parent

    def visit_Conditional(
        self, block: sbb.Conditional, blocks: BlockMapping
    ) -> sbb.BasicBlock:
        if block.first_line not in self.lines:
            return self.visit_block(block.parent, blocks)
        else:
            return sbb.Conditional(
                number=block.number,
                first_line=block.first_line,
                last_line=block.last_line,
                parent=self.visit_block(block.parent, blocks),
                conditional=block.conditional,
                true_branch=self.visit_block(block.true_branch, blocks),
                false_branch=self.visit_block(block.false_branch, blocks),
            )


def filter_lines(lines: Set[int], module: sbb.Module) -> sbb.Request:
    print(f"Filtering on lines {lines}")
    filtered = LineFilterer(lines).visit_Module(module)
    print("filtered code", filtered.code)
    return filtered
