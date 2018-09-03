from . import ssa_basic_blocks as sbb
from .visitor import UpdateVisitor


class ConditionalElimination(UpdateVisitor):
    def visit_Conditional(self, cond: sbb.Conditional) -> sbb.BasicBlock:
        if isinstance(cond.true_branch, sbb.TrueBranch) and isinstance(
            cond.false_branch, sbb.FalseBranch
        ):
            return self.visit(cond.parent)
        else:
            return super().generic_visit(cond)
