from __future__ import annotations

from typing import Iterable, Optional, Sequence, Set, Tuple

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

    def __or__(self, other: object) -> TargetManager:
        if isinstance(other, TargetManager):
            return TargetManager(self.targets | other.targets)
        elif isinstance(other, Iterable):
            return TargetManager(self.targets.union(other))
        raise TypeError(f"Cannot `or` TargetManager with {type(other)}")

    __ror__ = __or__

    def __and__(self, other: object) -> TargetManager:
        if isinstance(other, TargetManager):
            return TargetManager(self.targets & other.targets)
        elif isinstance(other, Iterable):
            return TargetManager(self.targets.intersection(other))
        raise TypeError(f"Cannot `and` TargetManager with {type(other)}")

    __rand__ = __and__

    def update(self, replacement: TargetManager) -> None:
        self.targets = replacement.targets

    def merge(self, other: TargetManager) -> None:
        self.targets |= other.targets

    def add(self, id: str, count: int) -> None:
        self.targets.add((id, count))
