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

    def visit_Loop(self, loop: sbb.Loop) -> sbb.BasicBlock:
        def empty_branch(loop: sbb.BasicBlock, parent: sbb.BasicBlock) -> bool:
            if parent is loop:
                return True
            return isinstance(loop, sbb.TrueBranch)
        # Filter out loops which do nothing:
        if all(empty_branch(l, loop.parent) for l in loop.loops):
            log.notice(f"Discarding loop on lines"
                       f" {loop.first_line}–{loop.last_line} because "
                       "all of the loop branches are empty")
            return self.visit(loop.parent)
        else:
            return super().generic_visit(loop)
