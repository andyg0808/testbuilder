import re
from typing import (
    Any,
    List,
    Mapping,
    MutableMapping as MMapping,
    Optional,
    Tuple,
    Union,
)

from logbook import Logger

import z3
from typeassert import assertify

from . import ssa_basic_blocks as sbb
from .pair import Pair
from .type_registrar import TypeRegistrar
from .z3_types import NilSort, Reference

# z3.set_param("model_compress", "false")
ModelItem = Union[z3.FuncInterp, z3.QuantifierRef]

VAR_NAME = re.compile(r"pyname_(.*)")

Solution = Mapping[str, Any]

StoreParser = re.compile(r"^store$|^store_(\d+)$")

log = Logger("solver")

DEFAULT_STORE = -1


Store = z3.QuantifierRef


class Z3PythonConverter:
    def __init__(self, model: z3.ModelRef, registrar: TypeRegistrar) -> None:
        self.cache: MMapping[str, z3.ExprRef] = {}
        self.store: Union[Mapper, NoneMapper]

        log.info(f"Converting model {model}")
        self.registrar = registrar

        # Mapping from variable names to Python values
        self._standardized: MMapping[str, Any] = {}

        stores = self.gather_stores(model)
        if stores:
            first_store = stores[0]
            log.info("Beginning store:", first_store)
            self.store = Mapper(first_store)
        else:
            self.store = NoneMapper()

        for k in model.decls():
            key = store_key(k)
            value = model[k]
            self._standardized[key] = self._z3_to_python(key, value)

    def _z3_to_python(self, store_key: str, value: ModelItem) -> Any:
        if store_key in self.cache:
            log.info(f"Found value in cache for {store_key}")
            return self.cache[store_key]
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
            if value.sort() == Reference:
                updated_value = value
                while self.is_reftype(updated_value):
                    updated_value = self.store[updated_value]
                log.info(
                    f"Dereferenced {store_key} with ref {value} to {updated_value}"
                )
                if updated_value is None:
                    return None
                return self._z3_to_python(str(value), updated_value)
            elif value.sort() == self.registrar.reftype:
                if value.decl() == self.registrar.reftype.Pair:
                    left, right = value.children()
                    # Invent store keys for now; we don't need them for non-reference values.
                    pair = Pair(None, None)
                    self.cache[store_key] = pair
                    pair.left = self._z3_to_python(store_key + ".left", left)
                    pair.right = self._z3_to_python(store_key + ".right", right)
                    return pair
            elif value.sort() == self.registrar.anytype:
                nil = getattr(self.registrar.anytype, "Nil", None)
                if value.decl() == nil.decl():
                    return None

            raise TypeError(f"Unknown datatype {value.decl()}")
        elif isinstance(value, z3.QuantifierRef):
            match = StoreParser.match(store_key)
            if match is not None:
                return value
            else:
                log.warn(
                    f"Unknown function interpretation {value} for"
                    f"key {store_key}; returning anyway"
                )
                return value
        # elif isinstance(value, z3.ExprRef):
        #     if value.sort() == NilSort:
        #         return None
        log.error(
            f"Couldn't find adapter for {store_key}; {value} has type {type(value)}"
        )
        sortname = str(value.sort())  # type: ignore
        raise TypeError(f"Couldn't find adapter for {type(value)} with sort {sortname}")

    def is_reftype(self, value: ModelItem) -> bool:
        if not isinstance(value, z3.DatatypeRef):
            return False
        return value.sort() == Reference

    def solution(self) -> Solution:
        return self._standardized

    def gather_stores(self, model: z3.ModelRef) -> List[Store]:
        """Given a Z3 model, finds all store variables present in it and
        returns a sorted list of them, starting with the
        lowest-numbered (i.e., `store`).

        Args:
            model: A model as produced by Z3's solver.

        Returns:
            A sorted list of QuantifierRefs. The first item in
            the list will be the lowest-numbered store found, and the
            last item will be the highest-numbered store found.
        """
        stores: List[Tuple[int, Store]] = []
        for k in model.decls():
            value = model[k]
            if isinstance(value, Store):
                match = StoreParser.match(store_key(k))
                if match is not None:
                    if match[1] is None:
                        number = 0
                    else:
                        number = int(match[1])
                    log.debug("Found store variable {}", number)
                    stores.append((number, value))
        stores.sort(key=lambda x: x[0])
        return [x[1] for x in stores]


def store_key(ref: z3.FuncDeclRef) -> str:
    key = VAR_NAME.fullmatch(ref.name())

    if key:
        return key[1]
    else:
        return ref.name()


@assertify
def solve(registrar: TypeRegistrar, data: sbb.TestData) -> Optional[Solution]:
    log.info("Solving expression {}", data.expression)
    solver = z3.Solver()
    solver.add(z3.simplify(data.expression))
    res = solver.check()
    if res == z3.unsat:
        return None
    model = solver.model()
    converter = Z3PythonConverter(model, registrar)
    return converter.solution()


class Mapper:
    def __init__(self, func: z3.QuantifierRef) -> None:
        self.lookup: MMapping[Any, Any] = {}
        self.func = func

    def __getitem__(self, key: z3.ExprRef) -> z3.ExprRef:
        lambda_var = z3.Var(0, self.func.var_sort(0))
        subst = z3.substitute(self.func.body(), (lambda_var, key))
        return z3.simplify(subst)


class NoneMapper:
    def __getitem__(self, key: z3.ExprRef) -> object:
        # Z3 has chosen to make some references when there is no
        # store. Return `None` for all the references
        log.notice(
            f"Substituting None for reference in {store_key} because no store exists"
        )
        return None
