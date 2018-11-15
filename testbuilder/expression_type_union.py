from typing import Any as PyAny

from dataclasses import dataclass

from .expandable_type_union import ExpandableTypeUnion
from .type_union import TypeUnion
from .z3_types import Expression


@dataclass(frozen=True)
class ExpressionTypeUnion(ExpandableTypeUnion):
    # `registrar` should actually be TypeRegistrar, but the import
    # loop makes Python sad.
    registrar: PyAny

    def expand(self) -> TypeUnion:
        return self.registrar.expand_reference(self)  # type: ignore
