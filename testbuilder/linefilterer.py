# from __future__ import annotations
import dataclasses
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
)

from logbook import Logger

from visitor import GenericVisitor, SearchVisitor, SetGatherVisitor, UpdateVisitor

from . import nodetree as n, ssa_basic_blocks as sbb
from .conditional_elimination import ConditionalElimination
from .coroutines import result, retrieve, run_to_suspend
from .target_manager import TargetManager

Coroutine = Generator[None, sbb.BasicBlock, sbb.BasicBlock]

log = Logger("linefilterer")


A = TypeVar("A", bound=sbb.BasicBlock)
B = TypeVar("B", bound=sbb.BasicBlock)
BlockMapping = MMapping[int, sbb.BasicBlock]
StopBlock = Optional[sbb.BasicBlock]
StoreMutation = ("StoreMutation", 0)


class ComputedLineFilterer(UpdateVisitor):
    def __init__(self, target_line: int) -> None:
        super().__init__()
        self.target_line = target_line

    def update_target(self, thing: Any) -> None:
        if self.target_line < 0:
            target = self.target_line + sbb.last_line(thing) + 1
            log.info(f"Updating target line from {self.target_line} to {target}")
            self.target_line = target

    def visit_Module(self, module: sbb.Module) -> Optional[sbb.Request]:
        self.update_target(module)
        for func in module.functions.values():
            updated = self.visit_FunctionDef(func)
            if updated is not None:
                assert isinstance(updated, sbb.FunctionDef)
                return sbb.Request(module=module, code=updated)
        blocktree = self.visit_BlockTree(module.code)
        if blocktree is None:
            return None
        assert isinstance(blocktree, sbb.BlockTree)
        return sbb.Request(module=module, code=blocktree)

    def visit_FunctionDef(self, function: sbb.FunctionDef) -> Optional[sbb.FunctionDef]:
        self.update_target(function)
        blocktree = self.visit_BlockTree(function.blocks)
        if blocktree is None or blocktree.empty():
            log.info(
                f"Discarding {function.name} because it is empty. "
                "This probably means it is unused in this test."
            )
            return None
        else:
            return dataclasses.replace(
                function,
                first_line=blocktree.start.line,
                last_line=blocktree.end.line,
                blocks=blocktree,
            )
        pass

    def visit_BlockTree(self, blocktree: sbb.BlockTree) -> Optional[sbb.BlockTree]:
        self.update_target(blocktree)
        target = Discovery(self.target_line)(blocktree.end)
        if target is None:
            return None
        filterer = Filter(self.target_line)
        filtered: sbb.BasicBlock = result(filterer(target), blocktree.start)
        tree: sbb.BasicBlock = ConditionalElimination()(filtered)
        start_block = blocktree.start
        return sbb.BlockTree(
            start=start_block,
            end=sbb.ReturnBlock(number=blocktree.end.number, parents=[tree]),
        )


class Discovery(SearchVisitor[sbb.BasicBlock]):
    def __init__(self, target_line: int) -> None:
        super().__init__()
        self.target_line = target_line
        log.info("Searching for line {}...", target_line)

    def visit_Positioned(self, block: sbb.Positioned) -> Optional[sbb.BasicBlock]:
        if self.target_line in block.lines:
            assert isinstance(block, sbb.BasicBlock)
            return block
        elif isinstance(block, sbb.Parented):
            return self.visit(block.parent)
        else:
            return None

    def visit_Controlled(self, block: sbb.Controlled) -> Optional[sbb.BasicBlock]:
        if self.target_line == block.line:
            assert isinstance(block, sbb.BasicBlock)
            return block
        elif isinstance(block, sbb.Parented):
            return self.visit(block.parent)
        else:
            return None


SSAName = Tuple[str, int]


class DepFinder(SetGatherVisitor[SSAName]):
    def visit_Name(self, name: n.Name) -> Set[SSAName]:
        return {(name.id, name.set_count)}

    def visit_Set(self, assign: n.Set) -> Set[SSAName]:
        deps = self.visit(assign.e)
        if isinstance(assign.target, n.Attribute):
            log.debug("adding target of attribute {}", assign.target)
            name = self.visit(assign.target.e)
            log.debug("found {} from attribute", name)
            deps |= name

        return deps


@singledispatch
def target_finder(obj: Any) -> Optional[SSAName]:
    return None


@target_finder.register(n.Set)
def find_Set_target(obj: n.Set) -> SSAName:
    if isinstance(obj.target, n.Attribute):
        # This is a hack to treat all attribute stores as desired
        # lines, due to aliasing problems.  If we don't do this, an
        # aliased name for a dependent variable appears not to be a
        # dependency, even though it can change the value of the
        # dependent variable.
        log.debug("Returning store mutation")
        return StoreMutation
    name = obj.target.find_name()
    return (name.id, name.set_count)


class Filter(GenericVisitor[Coroutine]):
    def __init__(self, target_line: int) -> None:
        super().__init__()
        self.target_line = target_line
        self.dep_finder = DepFinder()

    def __call__(self, v: Any, *args: Any, **kwargs: Any) -> Coroutine:
        return self.visit(v, None, TargetManager({StoreMutation}), *args, **kwargs)

    def visit_Code(
        self, code: sbb.Code, stop: StopBlock, targets: TargetManager
    ) -> Coroutine:
        if code is stop:
            return (yield)
        lines: List[n.stmt] = []
        # We have to work up from the bottom
        for line in reversed(code.code):
            target = target_finder(line)
            if self.keep_line(line, target in targets):
                deps = self.dep_finder(line)
                lines.insert(0, line)
                if target != StoreMutation:
                    targets.replace(target, deps)
                else:
                    targets.replace(None, deps)
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

    def keep_line(self, line: n.stmt, in_targets: bool) -> bool:
        return line.line == self.target_line or in_targets or isinstance(line, n.Assert)

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

    def visit_Controlled(
        self, controller: sbb.Controlled, stop: sbb.BasicBlock, targets: TargetManager
    ) -> Coroutine:
        if controller is stop:
            return (yield)
        deps = self.dep_finder(controller.conditional)
        targets.merge(TargetManager(set(deps)))
        return (yield from self.visit_block(controller, stop, targets))

    def generic_visit(self, v: sbb.BasicBlock, *args: Any, **kwargs: Any) -> Coroutine:
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
        return v.__class__(**results)


class FunctionChooser(ComputedLineFilterer):
    def visit_Module(self, module: sbb.Module) -> Optional[sbb.Request]:
        self.update_target(module)
        for func in module.functions.values():
            updated = self.visit_FunctionDef(func)
            if updated is not None:
                assert isinstance(updated, sbb.FunctionDef)
                return sbb.Request(module=module, code=func)
            else:
                log.notice(f"Throwing out `{func.name}` because no lines were kept")
        blocktree = self.visit_BlockTree(module.code)
        if blocktree is None:
            return None
        assert isinstance(blocktree, sbb.BlockTree)
        return sbb.Request(module=module, code=module.code)


def filter_lines(
    target_line: int, module: sbb.Module, slice: bool = True
) -> Optional[sbb.Request]:
    log.info(f"Filtering starting at line {target_line}")
    if slice:
        filtered = ComputedLineFilterer(target_line).visit_Module(module)
    else:
        filtered = FunctionChooser(target_line).visit_Module(module)
    return filtered
