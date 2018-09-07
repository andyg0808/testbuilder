# from __future__ import annotations
from collections.abc import Iterable
from copy import copy
from functools import singledispatch
from typing import (
    Any,
    Generator,
    List,
    MutableMapping as MMapping,
    Optional,
    Set,
    Tuple,
    TypeVar,
    cast,
)

from logbook import Logger, StderrHandler

import dataclasses

from . import nodetree as n, ssa_basic_blocks as sbb
from .conditional_elimination import ConditionalElimination
from .coroutines import result, retrieve, run_to_suspend
from .target_manager import TargetManager
from .visitor import GatherVisitor, GenericVisitor, SearchVisitor, UpdateVisitor

Coroutine = Generator[None, sbb.BasicBlock, sbb.BasicBlock]

log = Logger("linefilterer")


StderrHandler(
    level="INFO", filter=lambda r, h: r.channel == "linefilterer"
).push_application()

A = TypeVar("A", bound=sbb.BasicBlock)
B = TypeVar("B", bound=sbb.BasicBlock)
BlockMapping = MMapping[int, sbb.BasicBlock]
StopBlock = Optional[sbb.BasicBlock]


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


class Filter(GenericVisitor[Coroutine]):
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

    def generic_visit(self, v: sbb.BasicBlock, *args: Any) -> Coroutine:
        assert isinstance(v, sbb.BasicBlock)
        return (yield from self.visit_block(v, *args))

    def visit_block(
        self, v: sbb.BasicBlock, stop: StopBlock, targets: TargetManager, **updates: Any
    ) -> Coroutine:
        if v is stop:
            return (yield)
        fields = dataclasses.fields(v)
        results: MMapping[str, Any] = {}
        for f in fields:
            if f.name.startswith("_"):
                continue
            elif f.name == "parent":
                continue
            data = getattr(v, f.name)
            res: Any
            if f.name in updates:
                res = updates[f.name]
            elif isinstance(data, sbb.BasicBlock) or isinstance(data, Iterable):
                raise RuntimeError(f"Unhandled basic block in field {f.name} ({data})")
            else:
                res = data
            results[f.name] = res
        parent = getattr(v, "parent", None)
        if parent:
            results["parent"] = yield from self.visit(parent, stop, targets)
        return cast(sbb.BasicBlock, v.__class__(**results))


def filter_lines(target_line: int, lines: Set[int], module: sbb.Module) -> sbb.Request:
    log.info(f"Filtering starting at line {target_line}")
    filtered = ComputedLineFilterer(target_line).visit_Module(module)
    return filtered
