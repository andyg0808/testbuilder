from dataclasses import dataclass
from typing import Any as PyAny, cast

from .type_union import TypeUnion
from .z3_types import AnyT, Expression


@dataclass(frozen=True)
class ExpandableTypeUnion(TypeUnion):
    # `registrar` should actually be TypeRegistrar, but the import
    # loop makes Python sad.
    registrar: PyAny

    def expand(self) -> TypeUnion:
        return self.registrar.expand(self.name, self.sorts)  # type: ignore

    def _get_any(self) -> AnyT:
        assert len(self.expressions) == 1
        expr = self.expressions[0].expr
        assert expr.sort() == self.registrar.anytype
        return cast(AnyT, expr)

    def unwrap(self, *args: PyAny) -> Expression:
        """
        Tries to unwrap directly; if that fails, expands, then unwraps.
        """
        try:
            return super().unwrap(*args)
        except AssertionError:
            return self.expand().unwrap(*args)
