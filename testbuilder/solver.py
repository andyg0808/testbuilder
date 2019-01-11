import re
from typing import Any, List, Mapping, MutableMapping as MMapping, Optional, Union, cast

from logbook import Logger

import z3
from typeassert import assertify

from . import ssa_basic_blocks as sbb
from .pair import Pair
from .type_registrar import TypeRegistrar
from .z3_types import Reference

# z3.set_param("model_compress", "false")
ModelItem = Union[z3.FuncInterp, z3.QuantifierRef]

VAR_NAME = re.compile(r"pyname_(.*)")

Solution = Mapping[str, Any]

StoreParser = re.compile(r"^store$|^store_(\d+)$")

log = Logger("solver")

DEFAULT_STORE = -1


class Z3PythonConverter:
    def __init__(self, model: z3.ModelRef, registrar: TypeRegistrar) -> None:
        log.info(f"Converting model {model}")
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
                log.notice(
                    "Assigning None to reference {} because no store exists", refkey
                )
                self._standardized[refkey] = None
        else:
            self.final_store = Mapper(self._standardized[self.max_store_name])

            # Dereference all references from the final store
            for refkey in self.refkeys:
                ref = self._standardized[refkey]
                value = ref
                while self.is_reftype(value):
                    value = self.final_store[value]  # type: ignore
                log.info(f"Dereferenced {refkey} with ref {ref} to {value}")
                self._standardized[refkey] = self._z3_to_python(refkey, value)

    def is_reftype(self, value: ModelItem) -> bool:
        if self.registrar.reftype is None:
            return False
        if not isinstance(value, z3.DatatypeRef):
            return False
        return value.sort() == Reference

    def solution(self) -> Solution:
        return self._standardized

    def _z3_to_python(self, store_key: str, value: ModelItem) -> Any:
        if isinstance(value, z3.DatatypeRef):
            if value.sort() == self.registrar.anytype:
                value = self.registrar.unwrap(value)
        if z3.is_int(value):
            return value.as_long()  # type: ignore
        elif z3.is_string(value):
            strvalue = value.as_string()  # type: ignore
            return strvalue[1:-1]
        elif z3.is_bool(value) and not isinstance(value, z3.QuantifierRef):
            return bool(value)
        elif isinstance(value, z3.DatatypeRef):
            if value.sort() == self.registrar.anytype:
                if value.decl() == self.registrar.anytype.none.decl():
                    return None
            elif value.sort() == Reference:
                self.refkeys.append(store_key)
                return value
            elif (
                self.registrar.reftype is not None
                and value.sort() == self.registrar.reftype
            ):
                if value.decl() == self.registrar.reftype.Pair:
                    left, right = value.children()
                    # Invent store keys for now; we don't need them for non-reference values.
                    return Pair(
                        self._z3_to_python(store_key + ".left", left),
                        self._z3_to_python(store_key + ".right", right),
                    )

            raise TypeError(f"Unknown datatype {value.decl()}")
        elif isinstance(value, z3.QuantifierRef):
            match = StoreParser.match(store_key)
            if match is not None:
                log.debug("match {} {}", store_key, match)
                if match[1] is None:
                    number = 0
                else:
                    number = int(match[1])

                log.debug("Found store variable {}", number)
                if number > self.max_store:
                    self.max_store = number
                    self.max_store_name = store_key
                return value
            else:
                log.warn(
                    f"Unknown function interpretation {value} for"
                    f"key {store_key}; ignoring"
                )
                return value
        log.error(
            f"Couldn't find adapter for {store_key}; {value} has type {type(value)}"
        )
        raise TypeError(f"Couldn't find adapter for {type(value)}")


@assertify
def solve(registrar: TypeRegistrar, data: sbb.TestData) -> Optional[Solution]:
    log.info("Solving expression {}", data.expression)
    solver = z3.Solver()
    solver.add(data.expression)
    res = solver.check()
    if res == z3.unsat:
        return None
    model = solver.model()
    converter = Z3PythonConverter(model, registrar)
    return converter.solution()


class Mapper:
    def __init__(self, func: z3.QuantifierRef) -> None:
        self.lookup: MMapping[Any, Any] = {}
        # self._else = func.else_value()
        self.func = func
        self._else = func.body()
        print("type", type(func.body()))

    def __getitem__(self, key: z3.ExprRef) -> z3.ExprRef:
        # print("getitem")
        # val = self.lookup.get(key, self._else)
        # return val
        subst = z3.substitute(self.func.body(), (z3.Var(0, self.func.var_sort(0)), key))
        # embed()
        return z3.simplify(subst)

    def elsevalue(self) -> Any:
        print("elsevalue")
        return self._else
