from __future__ import annotations

from typing import Optional, cast

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
            name = f"{name_part}_{self.index}"
        else:
            name = f"Any_{self.index}"
        self.name = name
        self.datatype = z3.Datatype(name)
        self.reftype: Optional[z3.Datatype] = None

    def wrappers(self) -> TypeBuilder:
        self.datatype.declare("Int", ("i", z3.IntSort()))
        self.datatype.declare("Bool", ("b", z3.BoolSort()))
        self.datatype.declare("String", ("s", z3.StringSort()))
        return self

    def none(self) -> TypeBuilder:
        self.datatype.declare("none")
        return self

    def references(self) -> TypeBuilder:
        self.datatype.declare("Reference", ("r", z3.IntSort()))
        self.reftype = z3.Datatype(self.name + "_reftypes")
        return self

    def structures(self) -> TypeBuilder:
        assert (
            self.reftype is not None
        ), "Must enable references in order to have structures"
        self.reftype.declare(
            "Pair", ("Pair_left", self.datatype), ("Pair_right", self.datatype)
        )
        return self

    def build(self) -> TypeRegistrar:
        if self.reftype is None:
            anytype = self.datatype.create()
            return TypeRegistrar(anytype, None)
        else:
            anytype, reftype = z3.CreateDatatypes(self.datatype, self.reftype)
            return TypeRegistrar(anytype, reftype)

    def construct(self) -> TypeRegistrar:
        self.none()
        self.references()
        self.wrappers()
        self.structures()
        return self.build()
