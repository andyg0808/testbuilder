import re
from typing import Any, Mapping, Optional

from typeassert import assertify

import z3

from . import ssa_basic_blocks as sbb
from .z3_types import Any as AnyType, unwrap

VAR_NAME = re.compile(r"pyname_(.*)")

Solution = Mapping[str, Any]


@assertify
def solve(data: sbb.TestData) -> Optional[Solution]:
    solver = z3.Solver()
    solver.add(data.expression)
    res = solver.check()
    if res == z3.unsat:
        return None
    # print("model", solver.model())
    # print("decls", solver.decls())
    standardized = {}
    model = solver.model()
    for k in model.decls():
        key = VAR_NAME.fullmatch(k.name())
        value = model[k]

        if key:
            store_key = key[1]
        else:
            store_key = k.name()

        pyvalue: Any
        if isinstance(value, z3.DatatypeRef):
            if value.sort() == AnyType:
                value = unwrap(value)
        if z3.is_int(value):
            pyvalue = value.as_long()
        elif z3.is_string(value):
            pyvalue = value.as_string()
            pyvalue = pyvalue[1:-1]
        elif z3.is_bool(value):
            pyvalue = bool(value)
        else:
            raise TypeError(f"Couldn't find adapter for {type(value)}")

        standardized[store_key] = pyvalue

    return standardized
