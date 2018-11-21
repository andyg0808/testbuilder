from typing import Optional, cast

from logbook import Logger

import z3
from dataclasses import dataclass

from .store_array import ArrayKey, ArrayVal, StoreArray
from .type_registrar import TypeRegistrar
from .z3_types import Reference

log = Logger("store")


@dataclass
class Store:
    registrar: TypeRegistrar
    _current_store: Optional[StoreArray] = None
    keys: int = 0
    store_number = 0
    written_number = 0

    @property
    def store(self) -> StoreArray:
        if self._current_store is None:
            self._current_store = self.registrar.store("store")
        return self._current_store

    @store.setter
    def store(self, value: StoreArray) -> None:
        self._current_store = value

    def add(self, value: ArrayVal) -> ArrayKey:
        key = Reference.Reference(z3.IntVal(self.keys))
        self.keys += 1
        self._set(key, value)
        return key

    def get(self, key: ArrayKey) -> ArrayVal:
        return self.store[key]

    def _set(self, key: ArrayKey, value: ArrayVal) -> None:
        self.store_number += 1
        self.store = cast(StoreArray, z3.Store(self.store, key, value))

    def pending(self) -> bool:
        return self.written_number < self.store_number

    def write(self) -> z3.Bool:
        log.info(f"Writing store {self.store_number} to replace {self.written_number}")
        self.written_number = self.store_number
        name = f"store_{self.written_number}"
        array_var = self.registrar.store(name)
        store = self.store
        self.store = array_var
        return array_var == store
