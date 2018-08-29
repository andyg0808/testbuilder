from typing import Optional, Set, Tuple

from . import nodetree as n, ssa_basic_blocks as sbb
from .visitor import UpdateVisitor

NameSet = Set[Tuple[str, int]]


class PhiFilterer(UpdateVisitor):
    def visit_Request(self, request: sbb.Request) -> sbb.Request:
        return sbb.Request(module=request.module, code=self.visit(request.code, set()))

    def visit_Name(self, name: n.Name, seen: NameSet) -> n.Name:
        seen.add((name.id, name.set_count))
        return name

    def visit_PhiSet(self, phiset: n.PhiSet, seen: NameSet) -> Optional[n.PhiSet]:
        target = phiset.target
        if (target.id, target.set_count) in seen:
            return phiset
        else:
            return None

    # TODO: Ensure that multi-path nodes get separate variable batches
    # for each path.

    def visit_Code(self, code: sbb.Code, seen: NameSet) -> sbb.BasicBlock:
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
