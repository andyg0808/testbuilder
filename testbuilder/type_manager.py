from copy import copy
from functools import reduce
from typing import List, MutableMapping as MMapping, Optional, Sequence

from logbook import Logger

from dataclasses import dataclass, field

from .z3_types import SortSet

SortMapping = MMapping[str, SortSet]

log = Logger("type_manager")


@dataclass
class TypeManager:
    type_list: SortMapping = field(default_factory=dict, init=False)
    stack: List[SortMapping] = field(default_factory=list, init=False)

    def get(self, name: str) -> Optional[SortSet]:
        return self.type_list.get(name, None)

    def put(self, name: str, value: Optional[set] = None) -> None:
        if value is None:
            value = set()
        self.type_list[name] = value

    def push(self) -> None:
        self.stack.append(copy(self.type_list))

    def pop(self) -> SortMapping:
        old = self.type_list
        self.type_list = self.stack.pop()
        return old

    def restore(self) -> None:
        self.type_list = copy(self.stack[-1])

    def merge_and_update(self, mappings: Sequence[SortMapping]) -> None:
        log.debug("mappings to start", mappings)
        if len(mappings) == 0:
            self.type_list = {}
            return
        keysets = [
            {k for k, v in mapping.items() if len(v) > 0} for mapping in mappings
        ]
        keys = reduce(lambda ks, m: ks & m, keysets)

        log.debug("keys", keys)
        new_mapping: SortMapping = {k: set() for k in keys}
        for mapping in mappings:
            for key in keys:
                current = mapping[key]
                assert len(current) != 0, "Key has empty value"
                new_mapping[key] |= current
                self.type_list = new_mapping
        log.debug("new mapping", self.type_list)
