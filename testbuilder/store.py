from dataclasses import dataclass
from typing import List, Optional, cast

import z3
from logbook import Logger

from .constrained_expression import ConstrainedExpression as CExpr
from .expandable_type_union import ExpandableTypeUnion
from .store_array import ArrayKey, ArrayVal, StoreArray
from .type_registrar import TypeRegistrar
from .type_union import TypeUnion
from .z3_types import Expression, Reference, bool_not

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

    def write(self) -> z3.BoolRef:
        log.info(f"Writing store {self.store_number} to replace {self.written_number}")
        self.written_number = self.store_number
        name = f"store_{self.written_number}"
        array_var = self.registrar.store(name)
        store = self.store
        self.store = array_var
        return array_var == store

    def to_boolean(self, value: TypeUnion, invert: bool = False) -> TypeUnion:
        """
        Convert all the expressions in this TypeUnion to booleans,
        applying truthy standards as needed in order to convert
        non-boolean types.
        """
        if isinstance(value, ExpandableTypeUnion):
            # Always want to work on expanded version, because a
            # VariableTypeUnion is either unconstrained or empty. If
            # unconstrained, we need to expand to get constrained
            # values. If empty, expanding gets the appropriate
            # constrained values.
            return self.to_boolean(value.expand(), invert)
        bools: List[CExpr] = []
        for cexpr in value.expressions:
            expr = self.expr_to_boolean(cexpr.expr)
            if invert:
                expr = bool_not(expr)
            bools.append(CExpr(expr=expr, constraints=cexpr.constraints))
        return TypeUnion(expressions=bools, sorts={z3.BoolSort()})

    def expr_to_boolean(self, expr: Expression) -> z3.BoolRef:
        """
        Apply Python's truthy standards to make a boolean of an
        expression.
        """
        if expr.sort() == Reference:
            ref = cast(ArrayKey, expr)
            log.info(f"Dereferencing {ref}")
            return self.expr_to_boolean(self.get(ref))
        else:
            return self.registrar.expr_to_boolean(expr)
