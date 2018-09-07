from typing import Sequence

from logbook import Logger, StderrHandler

from . import ssa_basic_blocks as sbb
from .visitor import UpdateVisitor

log = Logger("conditional_elimination")
StderrHandler(
    level="INFO", filter=lambda r, h: r.channel == "conditional_elimination"
).push_application()


class ConditionalElimination(UpdateVisitor):
    def visit_Conditional(self, cond: sbb.Conditional) -> sbb.BasicBlock:
        if empty_conditional(cond.parent, [cond.true_branch, cond.false_branch]):
            log.notice(
                f"Discarding conditional on lines"
                f" {cond.first_line}–{cond.last_line} because it is empty"
            )
            return self.visit(cond.parent)
        else:
            return super().generic_visit(cond)

    def visit_Loop(self, loop: sbb.Loop) -> sbb.BasicBlock:
        # Filter out loops which do nothing:
        if empty_conditional(loop.parent, loop.loops):
            log.notice(
                f"Discarding loop on lines"
                f" {loop.first_line}–{loop.last_line} because "
                "all of the loop branches are empty"
            )
            return self.visit(loop.parent)
        else:
            return super().generic_visit(loop)


def empty_conditional(
    parent: sbb.BasicBlock, branches: Sequence[sbb.BasicBlock]
) -> bool:
    """
    Checks a list of branches and returns True if they are all empty.

    Empty is defined as either the first block in the branch is a
    TrueBlock or a FalseBlock, or the first block in the branch is the
    one passed as `parent` (i.e., the branch is in fact completely empty).
    The algorithm used here only makes sense if the TrueBlock or
    FalseBlock can be guaranteed to be the child of the block passed
    as `parent`, which is the standard location used by `ast_to_ssa`.
    """

    def empty_branch(branch: sbb.BasicBlock) -> bool:
        if parent is branch:
            return True
        return type(branch) == sbb.TrueBranch or type(branch) == sbb.FalseBranch

    return all(empty_branch(l) for l in branches)
