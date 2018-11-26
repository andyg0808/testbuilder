from dataclasses import dataclass

from .expandable_type_union import ExpandableTypeUnion
from .z3_types import AnyT


@dataclass(frozen=True)
class VariableTypeUnion(ExpandableTypeUnion):
    name: str

    def _get_any(self) -> AnyT:
        return self.registrar.make_any(self.name)  # type: ignore
