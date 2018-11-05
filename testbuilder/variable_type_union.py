from typing import Any as PyAny

from dataclasses import dataclass

from .type_union import TypeUnion
from .z3_types import AnyT, Expression


@dataclass(frozen=True)
class VariableTypeUnion(TypeUnion):
    name: str

    # `registrar` should actually be TypeRegistrar, but the import
    # loop makes Python sad.
    registrar: PyAny

    def _get_any(self) -> AnyT:
        return self.registrar.make_any(self.name)  # type: ignore

    def expand(self) -> TypeUnion:
        return self.registrar.expand(self.name, self.sorts)  # type: ignore

    def unwrap(self, *args: PyAny) -> Expression:
        """
        Tries to unwrap directly; if that fails, expands, then unwraps.
        """
        try:
            return super().unwrap(*args)
        except AssertionError:
            return self.expand().unwrap(*args)
