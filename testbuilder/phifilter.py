import dataclasses
from copy import copy
from typing import Optional

from visitor import UpdateVisitor

from . import nodetree as n, ssa_basic_blocks as sbb
from .target_manager import TargetManager


class PhiFilterer(UpdateVisitor):
    """
    Discards `PhiSet`s which are no longer needed because their
    destination variables are not used after assignment.
    """

    def visit_Request(self, request: sbb.Request) -> sbb.Request:
        return dataclasses.replace(
            request, code=self.visit(request.code, TargetManager())
        )

    def visit_Name(self, name: n.Name, seen: TargetManager) -> n.Name:
        seen.add(name.id, name.set_count)
        return name

    def visit_PhiSet(self, phiset: n.PhiSet, seen: TargetManager) -> Optional[n.PhiSet]:
        target = phiset.target
        name = target.find_name()
        if (name.id, name.set_count) in seen:
            return phiset
        else:
            return None

    def visit_Conditional(
        self, cond: sbb.Conditional, seen: TargetManager
    ) -> sbb.Conditional:
        true_seen = copy(seen)
        false_seen = copy(seen)
        true_branch = self.visit(cond.true_branch, true_seen)
        false_branch = self.visit(cond.false_branch, false_seen)
        seen.update(true_seen | false_seen)
        return sbb.Conditional(
            number=cond.number,
            first_line=cond.first_line,
            last_line=cond.last_line,
            parent=self.visit(cond.parent, seen),
            true_branch=true_branch,
            false_branch=false_branch,
        )

    def visit_Loop(self, loop: sbb.Loop, seen: TargetManager) -> sbb.Loop:
        loops = []
        post_seen = TargetManager()
        for l in loop.loops:
            iter_seen = copy(seen)
            loops.append(self.visit(l, iter_seen))
            post_seen.merge(iter_seen)
        seen.update(post_seen)
        return sbb.Loop(
            number=loop.number,
            first_line=loop.first_line,
            last_line=loop.last_line,
            parent=self.visit(loop.parent, seen),
            loops=loops,
        )

    def visit_Controlled(
        self, node: sbb.Controlled, seen: TargetManager
    ) -> sbb.Controlled:
        # Make sure to visit condition before visiting parent. Because
        # we are only adding items to a set, it won't matter that we
        # visit it twice
        self.visit(node.conditional, seen)
        return self.generic_visit(node, seen)

    def visit_Code(self, code: sbb.Code, seen: TargetManager) -> sbb.BasicBlock:
        visited = [self.visit(l, seen) for l in code.code]
        filtered = [l for l in visited if l is not None]
        parent = self.visit(code.parent, seen)
        if filtered:
            return sbb.Code(
                number=code.number,
                first_line=code.first_line,
                last_line=code.last_line,
                parent=parent,
                code=filtered,
            )
        else:
            return parent
