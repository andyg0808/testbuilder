from __future__ import annotations

from typing import cast

import z3

from .type_registrar import TypeRegistrar
from .z3_types import AnySort


class TypeBuilder:
    any_index = 0

    def __init__(self, name_part: str = "") -> None:
        TypeBuilder.any_index += 1
        self.index = TypeBuilder.any_index
        print(f"Starting new TypeBuilder with index {self.index}")
        if name_part:
            self.datatype = z3.Datatype(f"{name_part}_{self.index}")
        else:
            self.datatype = z3.Datatype(f"Any_{self.index}")

    def wrappers(self) -> TypeBuilder:
        self.datatype.declare("Int", ("i", z3.IntSort()))
        self.datatype.declare("Bool", ("b", z3.BoolSort()))
        self.datatype.declare("String", ("s", z3.StringSort()))
        return self

    def none(self) -> TypeBuilder:
        self.datatype.declare("none")
        return self

    def structures(self) -> TypeBuilder:
        self.datatype.declare(
            "Pair", ("Pair_left", self.datatype), ("Pair_right", self.datatype)
        )
        return self

    def build(self) -> TypeRegistrar:
        return TypeRegistrar(cast(AnySort, self.datatype.create()))

    def construct(self) -> TypeRegistrar:
        self.none()
        self.wrappers()
        self.structures()
        return self.build()
