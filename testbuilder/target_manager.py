from __future__ import annotations
from typing import Tuple, Set, Sequence, Optional
from dataclasses import dataclass, field

SSAName = Tuple[str, int]


@dataclass
class TargetManager:
    targets: Set[SSAName] = field(default_factory=set)

    def replace(self, target: Optional[SSAName], deps: Sequence[SSAName]) -> None:
        if target:
            self.targets = (self.targets - {target}) | set(deps)
        else:
            self.targets = self.targets | set(deps)

    def __contains__(self, obj: Optional[SSAName]) -> bool:
        if obj is None:
            return False
        else:
            return obj in self.targets

    def __or__(self, other: TargetManager) -> TargetManager:
        return TargetManager(self.targets | other.targets)

    def update(self, replacement: TargetManager) -> None:
        self.targets = replacement.targets

    def merge(self, other: TargetManager) -> None:
        self.targets |= other.targets
