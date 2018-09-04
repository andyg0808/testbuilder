from . import ssa_basic_blocks as sbb
from .visitor import UpdateVisitor
from logbook import Logger, StderrHandler
log = Logger('conditional_elimination')
StderrHandler(
    level="INFO", filter=lambda r, h: r.channel == "conditional_elimination"
).push_application()

class ConditionalElimination(UpdateVisitor):
    def visit_Conditional(self, cond: sbb.Conditional) -> sbb.BasicBlock:
        if isinstance(cond.true_branch, sbb.TrueBranch) and isinstance(
            cond.false_branch, sbb.FalseBranch
        ):
            log.notice(f"Discarding conditional on lines"
                       f" {cond.first_line}–{cond.last_line} because it is empty")
            return self.visit(cond.parent)
        else:
            return super().generic_visit(cond)
