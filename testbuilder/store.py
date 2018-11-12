from typing import Optional

import z3
from dataclasses import dataclass

from .type_registrar import TypeRegistrar
from .z3_types import Expression

# @dataclass(frozen=True)
# class StoreStore:
#     address: int
#     value: Expression


@dataclass
class Store:
    registrar: TypeRegistrar
    _current_store: Optional[z3.ArrayRef] = None
    keys: int = 0
    store_number = 0
    written_number = 0
    # values: MMapping[int, Expression] = field(default_factory=dict)
    # queue: List[Expression] = field(default_factory=list)

    @property
    def store(self) -> z3.ArrayRef:
        if self._current_store is None:
            self._current_store = self.registrar.store("store")
        return self._current_store

    @store.setter
    def store(self, value: z3.ArrayRef) -> None:
        self._current_store = value

    def add(self, value: Expression) -> int:
        key = self.keys
        self.keys += 1
        # self.values[key] = value
        # self.queue.append(StoreStore(key, value))
        # extract = getattr(self.registrar.anytype, "r")
        # keyexpr = extract(self.registrar.make_any(key))
        self._set(key, value)
        return key

    def _set(self, key: int, value: Expression) -> None:
        self.store_number += 1
        self.store = z3.Store(self.store, z3.IntVal(key), value)

    def pending(self) -> bool:
        return self.written_number < self.store_number

    def write(self) -> z3.Bool:
        self.written_number = self.store_number
        name = f"store_{self.written_number}"
        array_var = self.registrar.store(name)
        store = self.store
        self.store = array_var
        return array_var == store
