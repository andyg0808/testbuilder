# from __future__ import annotations
from copy import copy
from functools import singledispatch
from typing import (
    Any,
    Generator,
    Callable,
    Generic,
    List,
    MutableMapping as MMapping,
    Optional,
    Set,
    Tuple,
    Type,
    TypeVar,
    cast,
)

from logbook import Logger, StderrHandler
from toolz import pipe

from typeassert import assertify

from . import nodetree as n, ssa_basic_blocks as sbb
from .conditional_elimination import ConditionalElimination
from .nodetree import AddedLine
from .target_manager import TargetManager
from .visitor import (
    GatherVisitor,
    SearchVisitor,
    SimpleVisitor,
    UpdateVisitor,
    GenericVisitor,
)
from .coroutines import result, run_to_suspend, retrieve


Coroutine = Generator[None, sbb.BasicBlock, sbb.BasicBlock]

log = Logger("linefilterer")


StderrHandler(
    level="INFO", filter=lambda r, h: r.channel == "linefilterer"
).push_application()

A = TypeVar("A", bound=sbb.BasicBlock)
B = TypeVar("B", bound=sbb.BasicBlock)
BlockMapping = MMapping[int, sbb.BasicBlock]
StopBlock = Optional[sbb.BasicBlock]


class Parentable(Generic[B]):
    def __init__(self, func: Callable[[sbb.BasicBlock], B], contained: Type) -> None:
        self.partial = func
        self.contained = contained

    def __call__(self, parent: sbb.BasicBlock) -> B:
        return self.partial(parent)

    def child(self, child: Callable[[sbb.BasicBlock], A]) -> "Parentable[A]":
        parent_partial = self.partial

        def parentable(parent: sbb.BasicBlock) -> A:
            parent_val = parent_partial(parent)
            return child(parent_val)

        return Parentable(parentable, getattr(child, "contained", object))


# Define an identity Parentable; useful as a do-nothing return value


class ComputedLineFilterer(UpdateVisitor):
    def __init__(self, target_line: int) -> None:
        super().__init__()
        self.target_line = target_line

    def visit_Module(self, module: sbb.Module) -> sbb.Request:
        for func in module.functions.values():
            updated = self.visit_FunctionDef(func)
            if updated is not None:
                assert isinstance(updated, sbb.FunctionDef)
                return sbb.Request(module=module, code=updated)
            else:
                log.notice(f"Throwing out `{func.name}` because no lines were kept")
        blocktree = self.visit_BlockTree(module.code)
        if blocktree is None:
            raise RuntimeError("No code lines selected")
        assert isinstance(blocktree, sbb.BlockTree)
        return sbb.Request(module=module, code=blocktree)

    def visit_FunctionDef(self, function: sbb.FunctionDef) -> Optional[sbb.FunctionDef]:
        blocktree = self.visit_BlockTree(function.blocks)
        if blocktree is None or blocktree.empty():
            log.notice("Discarding function because it is empty")
            return None
        else:
            return sbb.FunctionDef(
                first_line=blocktree.start.line,
                last_line=blocktree.end.line,
                name=function.name,
                args=function.args,
                blocks=blocktree,
            )
        pass

    def visit_BlockTree(self, blocktree: sbb.BlockTree) -> Optional[sbb.BlockTree]:
        target = Discovery(self.target_line)(blocktree.end)
        if target is None:
            return None
        filterer = Filter(self.target_line)
        filtered: sbb.BasicBlock = result(filterer(target), blocktree.start)
        tree: sbb.BasicBlock = ConditionalElimination()(filtered)
        # print("Visited nodes", [type(node) for node in filterer.visited_nodes.values()])
        print("filtered", tree)
        start_block = blocktree.start
        return sbb.BlockTree(
            start=start_block,
            end=sbb.ReturnBlock(number=blocktree.end.number, parents=[tree]),
        )


class Discovery(SearchVisitor[sbb.BasicBlock]):
    def __init__(self, target_line: int) -> None:
        super().__init__()
        self.target_line = target_line
        print("searching for line", target_line)

    def visit_Positioned(self, block: sbb.Positioned) -> Optional[sbb.BasicBlock]:
        if self.target_line in block.lines:
            assert isinstance(block, sbb.BasicBlock)
            return block
        elif isinstance(block, sbb.Parented):
            return self.visit(block.parent)
        else:
            return None


SSAName = Tuple[str, int]


class DepFinder(GatherVisitor[SSAName]):
    def visit_Name(self, name: n.Name) -> List[SSAName]:
        return [(name.id, name.set_count)]

    def visit_Set(self, assign: n.Set) -> List[SSAName]:
        return self.visit(assign.e)


@singledispatch
def target_finder(obj: Any) -> Optional[SSAName]:
    return None


@target_finder.register(n.Set)
def find_Set_target(obj: n.Set) -> SSAName:
    return (obj.target.id, obj.target.set_count)


class Filter(SimpleVisitor[Coroutine]):
    def __init__(self, target_line: int) -> None:
        super().__init__()
        self.target_line = target_line
        self.dep_finder = DepFinder()

    def __call__(self, block: Any, *args: Any) -> Coroutine:
        return self.visit(block, None, TargetManager(), *args)

    def visit_Code(
        self, code: sbb.Code, stop: StopBlock, targets: TargetManager
    ) -> Coroutine:
        if code is stop:
            return (yield)
        print("-------------\nvisiting code block")
        lines: List[n.stmt] = []
        # We have to work up from the bottom
        for line in reversed(code.code):
            print("targets", targets)
            target = target_finder(line)
            print("target", target)
            if line.line == self.target_line or target in targets:
                # print("target info", target in targets, target, targets)
                # assert target is not None
                deps = self.dep_finder(line)
                print("deps on line", line.line, deps)
                lines.insert(0, line)
                targets.replace(target, deps)
                print("new targets", targets)
            else:
                print("Line discarded", line, target, targets, self.target_line)
                continue

        parent = yield from self.visit(code.parent, stop, targets)
        if not lines:
            return parent
        return sbb.Code(
            number=code.number,
            first_line=code.first_line,
            last_line=code.last_line,
            parent=parent,
            code=lines,
        )

    def visit_StartBlock(
        self, start: sbb.StartBlock, stop: StopBlock, targets: TargetManager
    ) -> Coroutine:
        if start is stop:
            return (yield)
        yield
        return start

    def visit_Conditional(
        self, cond: sbb.Conditional, stop: sbb.BasicBlock, targets: TargetManager
    ) -> Coroutine:
        if cond is stop:
            return (yield)
        true_targets = copy(targets)
        false_targets = copy(targets)
        true_branch: Coroutine = run_to_suspend(
            self.visit(cond.true_branch, cond.parent, true_targets)
        )
        false_branch: Coroutine = run_to_suspend(
            self.visit(cond.false_branch, cond.parent, false_targets)
        )
        targets.update(true_targets | false_targets)
        parent = yield from self.visit(cond.parent, stop, targets)
        return sbb.Conditional(
            number=cond.number,
            first_line=cond.first_line,
            last_line=cond.last_line,
            parent=parent,
            true_branch=retrieve(true_branch, parent),
            false_branch=retrieve(false_branch, parent),
        )

    def visit_Loop(
        self, loop: sbb.Loop, stop: sbb.BasicBlock, targets: TargetManager
    ) -> Coroutine:
        if loop is stop:
            return (yield)
        loops = []
        post_targets = TargetManager()
        for l in loop.loops:
            branch_targets = copy(targets)
            loops.append(run_to_suspend(self.visit(l, loop.parent, branch_targets)))
            post_targets.merge(branch_targets)
        targets.update(post_targets)
        parent = yield from self.visit(loop.parent, stop, targets)
        completed_loops = [retrieve(l, parent) for l in loops]
        return sbb.Loop(
            number=loop.number,
            first_line=loop.first_line,
            last_line=loop.last_line,
            parent=parent,
            loops=completed_loops,
        )

    def visit_TrueBranch(
        self, branch: sbb.TrueBranch, stop: StopBlock, targets: TargetManager
    ) -> Coroutine:
        if branch is stop:
            return (yield)

        parent = yield from self.visit(branch.parent, stop, targets)
        return sbb.TrueBranch(
            number=branch.number,
            conditional=branch.conditional,
            parent=parent,
            line=branch.line,
        )

    def visit_FalseBranch(
        self, branch: sbb.FalseBranch, stop: StopBlock, targets: TargetManager
    ) -> Coroutine:
        if branch is stop:
            return (yield)

        parent = yield from self.visit(branch.parent, stop, targets)
        return sbb.FalseBranch(
            number=branch.number,
            conditional=branch.conditional,
            parent=parent,
            line=branch.line,
        )


# def generic_visit(
#     self, v: A, stop: StopBlock, targets: Set[SSAName]
# ) -> Generator[None, sbb.StartBlock, A]:
#     try:
#         fields = dataclasses.fields(v)
#     except TypeError as err:
#         # If we are trying to look for fields on something
#         # that isn't a dataclass, it's probably a primitive
#         # field type, so just stop here.
#         return v
#     results: MMapping[str, Any] = {}
#     for f in fields:
#         if f.name.startswith("_"):
#             continue
#         data = getattr(v, f.name)
#         res: Any
#         if isinstance(data, list):
#             res = [self.visit(x, *args) for x in data]
#         else:
#             res = self.visit(data, *args)
#         results[f.name] = res
#     return cast(A, v.__class__(**results))


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
        if blocktree.empty():
            log.notice("Discarding function because it is empty")
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
        # contained_lines = sbb.line_range(block.parent, block)
        # print("contained_lines", contained_lines)
        # if (
        #     not self.lines.intersection(contained_lines)
        #     or block.first_line not in self.lines
        # ):
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
    # filtered = LineFilterer(lines, target_line).visit_Module(module)
    filtered = ComputedLineFilterer(target_line).visit_Module(module)
    return filtered
