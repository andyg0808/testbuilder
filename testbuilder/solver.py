import re
from typing import Any, List, Mapping, MutableMapping as MMapping, Optional

from logbook import Logger
from typeassert import assertify

import z3

from . import ssa_basic_blocks as sbb
from .type_registrar import TypeRegistrar
from .z3_types import Expression, Reference

VAR_NAME = re.compile(r"pyname_(.*)")

Solution = Mapping[str, Any]

StoreParser = re.compile(r"store|store_(\d+)")

log = Logger("solver")

DEFAULT_STORE = -1


class Z3PythonConverter:
    def __init__(self, model: z3.ModelRef, registrar: TypeRegistrar) -> None:
        self.registrar = registrar

        # Mapping from variable names to Python values
        self._standardized: MMapping[str, Any] = {}

        # Stores list of variable names which contain References
        self.refkeys: List[str] = []

        # The largest number store which has been discovered
        self.max_store = DEFAULT_STORE
        self.max_store_name = ""

        for k in model.decls():
            key = VAR_NAME.fullmatch(k.name())
            value = model[k]

            if key:
                store_key = key[1]
            else:
                store_key = k.name()

            self._standardized[store_key] = self._z3_to_python(store_key, value)

        if self.max_store == DEFAULT_STORE:
            # Z3 has chosen to make some references when there is no
            # store. Return `None` for all the references
            for refkey in self.refkeys:
                self._standardized[refkey] = None
        else:
            self.final_store = Mapper(self._standardized[self.max_store_name])

            # Dereference all references from the final store
            for refkey in self.refkeys:
                ref = self._standardized[refkey]
                value = ref
                while self.is_reftype(value):
                    value = self.final_store[value]
                print("found value", refkey, ref, value)
                self._standardized[refkey] = value

    def is_reftype(self, value: z3.FuncInterp) -> bool:
        if self.registrar.reftype is None:
            return False
        if not isinstance(value, z3.DatatypeRef):
            return False
        return value.sort() == self.registrar.reftype

    def solution(self) -> Solution:
        return self._standardized

    def _z3_to_python(self, store_key: str, value: z3.FuncInterp) -> Any:
        if isinstance(value, z3.DatatypeRef):
            if value.sort() == self.registrar.anytype:
                value = self.registrar.unwrap(value)
        if z3.is_int(value):
            return value.as_long()
        elif z3.is_string(value):
            strvalue = value.as_string()
            return strvalue[1:-1]
        elif z3.is_bool(value):
            return bool(value)
        elif isinstance(value, z3.DatatypeRef):
            if value.sort() == self.registrar.anytype:
                if value.decl() == self.registrar.anytype.none.decl():
                    return None
            elif value.sort() == Reference:
                self.refkeys.append(store_key)
                return value
        elif isinstance(value, z3.FuncInterp):
            match = StoreParser.match(store_key)
            if match is not None:
                if match[1] is None:
                    number = 0
                else:
                    number = int(match[1])

                print("found store variable", number)
                print("store for")
                if number > self.max_store:
                    self.max_store = number
                    self.max_store_name = store_key
                return value
            else:
                log.warn(
                    f"Unknown function interp {value} for key {store_key}; ignoring"
                )
                return value
        log.error(
            f"Couldn't find adapter for {store_key}; "
            "{value} has type {type(value)}, "
            "decl {value.decl()}, "
            "and sort {value.sort()}"
        )
        raise TypeError(f"Couldn't find adapter for {type(value)}")


@assertify
def solve(registrar: TypeRegistrar, data: sbb.TestData) -> Optional[Solution]:
    solver = z3.Solver()
    solver.add(data.expression)
    res = solver.check()
    if res == z3.unsat:
        return None
    model = solver.model()
    converter = Z3PythonConverter(model, registrar)
    return converter.solution()


class Mapper:
    def __init__(self, func: z3.FuncInterp) -> None:
        self.lookup: MMapping[Any, Any] = {}
        self._else = func.else_value()

    def __getitem__(self, key: Any) -> Any:
        pass

    def elsevalue(self) -> Any:
        return self._else
