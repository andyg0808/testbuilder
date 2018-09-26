from __future__ import annotations

from functools import singledispatch
from typing import cast

import z3

Expression = z3.ExprRef


class AnyT(z3.DatatypeRef):
    ...


class AnySort(z3.DatatypeSortRef):
    @staticmethod
    def Int(i: z3.Int) -> AnyT:
        ...

    @staticmethod
    def i(v: AnyT) -> z3.Int:
        ...

    @staticmethod
    def is_Int(v: Expression) -> bool:
        ...

    @staticmethod
    def Bool(i: z3.Bool) -> AnyT:
        ...

    @staticmethod
    def b(v: AnyT) -> z3.Bool:
        ...

    @staticmethod
    def is_Bool(v: Expression) -> bool:
        ...


AnyDatatype = z3.Datatype("Any")
AnyDatatype.declare("Int", ("i", z3.IntSort()))
AnyDatatype.declare("Bool", ("b", z3.BoolSort()))
Any: AnySort = cast(AnySort, AnyDatatype.create())


def make_any(name: str) -> Expression:
    return z3.Const(name, Any)
