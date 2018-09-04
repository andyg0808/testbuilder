from typing import MutableMapping as MMapping, Optional, Set, TypeVar, cast

from logbook import Logger, StderrHandler

from typeassert import assertify

from . import ssa_basic_blocks as sbb
from .nodetree import AddedLine
from .visitor import UpdateVisitor

log = Logger("linefilterer")


StderrHandler(
    level="INFO", filter=lambda r, h: r.channel == "linefilterer"
).push_application()

BlockMapping = MMapping[int, sbb.BasicBlock]

B = TypeVar("B", bound=sbb.BasicBlock)


class LineFilterer(UpdateVisitor):
    def __init__(self, lines: Set[int], target_line: int) -> None:
        super().__init__()
        self.lines = lines
        self.min_line = min(lines)
        self.max_line = max(lines)
        self.line_range = range(self.min_line, self.max_line + 1)
        self.target_line: int = target_line

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
                    log.notice(
                        f"Throwing out {func} because {func.lines} > "
                        f"{self.max_line}"
                    )
                    continue
            start = min(func.lines)
            end = max(func.lines)
            if start > self.max_line or end < self.min_line:
                log.notice(
                    f"Throwing out {func} because {start}>{self.max_line}"
                    f" or {end} < {self.min_line}"
                )
                continue
            res = self.visit_FunctionDef(func)
            if res is not None:
                code.append(res)
            else:
                log.notice("Throwing out {func} because no lines were kept")

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
        targeted = []
        for parent in parents:
            lines = sbb.lines(parent)
            if self.target_line in lines:
                targeted.append(parent)
        if targeted:
            parents = targeted
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
            log.debug("Found", block.number)
            return cast(B, blocks[block.number])
        else:
            log.debug("Visiting", block.number)
            newblock = self.visit(block, blocks)
            blocks[block.number] = newblock
            return newblock

    def visit_Code(self, code: sbb.Code, blocks: BlockMapping) -> sbb.BasicBlock:
        parent = self.visit_block(code.parent, blocks)
        body = [i for i in code.code if i.line in self.lines or i.line == AddedLine]
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
            parent = self.visit_block(block.parent, blocks)
            true_branch = self.visit_block(block.true_branch, blocks)
            false_branch = self.visit_block(block.false_branch, blocks)
            # If the target line is within a branch, we want to force
            # execution down that direction.
            if self.target_line in sbb.line_range(parent, true_branch):
                return true_branch
            if self.target_line in sbb.line_range(parent, false_branch):
                return false_branch
            return sbb.Conditional(
                number=block.number,
                first_line=block.first_line,
                last_line=block.last_line,
                parent=parent,
                true_branch=true_branch,
                false_branch=false_branch,
            )

    def visit_Loop(self, block: sbb.Loop, blocks: BlockMapping) -> sbb.BasicBlock:
        if block.first_line not in self.lines:
            log.debug("dropping loop")
            return self.visit_block(block.parent, blocks)
        if len(block.loops) == 0:
            raise RuntimeError("No loops present.")
        elif len(block.loops) == 1:
            return self.visit_block(block.loops[0], blocks)
        else:
            parent = self.visit_block(block.parent, blocks)
            loops = [self.visit_block(loop, blocks) for loop in block.loops]
            for loop in loops:
                if self.target_line in sbb.line_range(parent, loop):
                    return loop
            return sbb.Loop(
                number=block.number,
                first_line=block.first_line,
                last_line=block.last_line,
                parent=parent,
                loops=loops,
            )

    def visit_TrueBranch(
        self, block: sbb.TrueBranch, blocks: BlockMapping
    ) -> sbb.BasicBlock:
        if block.line not in self.lines:
            return self.visit_block(block.parent, blocks)
        else:
            return super().generic_visit(block, blocks)

    def visit_FalseBranch(
        self, block: sbb.FalseBranch, blocks: BlockMapping
    ) -> sbb.BasicBlock:
        if block.line not in self.lines:
            return self.visit_block(block.parent, blocks)
        else:
            return super().generic_visit(block, blocks)

    def visit_WhileFalseBranch(
        self, block: sbb.WhileFalseBranch, blocks: BlockMapping
    ) -> sbb.BasicBlock:
        if self.target_line < block.controlled_line or block.line not in self.lines:
            return self.visit_block(block.parent, blocks)
        else:
            return super().generic_visit(block, blocks)


def filter_lines(target_line: int, lines: Set[int], module: sbb.Module) -> sbb.Request:
    log.info(f"Filtering on lines {lines}")
    filtered = LineFilterer(lines, target_line).visit_Module(module)
    return filtered
