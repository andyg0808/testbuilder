import re
from typing import Any, Mapping, Optional

import z3
from typeassert import assertify

VAR_NAME = re.compile(r"pyname_(.*)")

Solution = Mapping[str, Any]


def solve(expr: z3.ExprRef) -> Optional[Solution]:
@assertify
    solver = z3.Solver()
    solver.add(expr)
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
        if z3.is_int(value):
            pyvalue = value.as_long()
        elif z3.is_string(value):
            pyvalue = value.as_string()
            pyvalue = pyvalue[1:-1]
        else:
            raise TypeError(f"Couldn't find adapter for {type(pyvalue)}")

        standardized[store_key] = pyvalue

    return standardized
