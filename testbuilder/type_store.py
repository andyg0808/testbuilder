from __future__ import annotations

from copy import copy
from typing import Mapping, MutableMapping as MMapping, Tuple

from dataclasses import dataclass, field

from . import nodetree as n
from .vartypes import AnyType, Types

SSAName = Tuple[str, int]
TypeMapping = Mapping[SSAName, Types]


def merge_types(left: Types, right: Types) -> Types:
    pass


@dataclass(frozen=True)
class TypeStore:
    block_types: MMapping[int, TypeMapping] = field(default_factory=dict)
    types: MMapping[SSAName, Types] = field(default_factory=dict)

    def merge(self, other: TypeStore) -> TypeStore:
        types = self._merge_types(other)
        block_types = self._merge_block_types(other)
        return TypeStore(block_types=block_types, types=types)

    def set(self, name: n.Name, t: Types) -> TypeStore:
        types = copy(self.types)
        types[format_name(name)] = t
        return TypeStore(types=types, block_types=copy(self.block_types))

    def get(self, name: n.Name) -> Types:
        return self.types.get(format_name(name), AnyType)

    def _merge_types(self, other: TypeStore) -> MMapping[SSAName, Types]:
        types = copy(self.types)
        for key, value in other.types.items():
            if key in types:
                types[key] |= value
            else:
                types[key] = value
        return types

    def _merge_block_types(self, other: TypeStore) -> MMapping[int, TypeMapping]:
        block_types = copy(self.block_types)
        for key, value in other.block_types.items():
            if key in block_types:
                assert block_types[key] == value
            else:
                block_types[key] = value
        return block_types


def format_name(name: n.Name) -> Tuple[str, int]:
    return (name.id, name.set_count)
