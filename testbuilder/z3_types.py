from __future__ import annotations

from dataclasses import dataclass, field
from functools import singledispatch
from typing import cast, MutableMapping as MMapping, Optional, TypeVar
from .visitor import SimpleVisitor

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

@dataclass
class TypeUnion:
    expressions: MMapping[z3.SortRef, Expression]
    constraint: MMapping[z3.SortRef, Expression] = field(default_factory=dict)

    def add(self, sort: z3.DatatypeSortRef, expr: Expression) -> None:
        self.expressions[sort] = expr

    def get(self, sort: z3.DatatypeSortRef) -> Optional[Expression]:
        return self.expressions.get(sort, None)

    @staticmethod
    def union(sort: z3.DatatypeSortRef, expr: Expression) -> TypeUnion:
        return TypeUnion({sort: expr})

    @staticmethod
    def Int(val: z3.Int) -> TypeUnion:
        return TypeUnion({z3.IntSort(): val})

    @staticmethod
    def Str(val: z3.StringVal) -> TypeUnion:
        return TypeUnion({z3.StringSort(): val})

    def to_expr(self) -> Expression:
        values = []
        for key, value in self.expressions.items():
            if key in self.constraint:
                value = z3.And(value, self.constraint[key])
                values.append(value)
        return z3.Or(*values)

def make_any(name: str) -> Expression:
    return z3.Const(name, Any)


def unwrap(val: Expression) -> Expression:
    if val.sort() == Any:
        if val.decl() in [Any.Bool, Any.Int]:
            # Extract the value from the wrapper
            return val.arg(0)
    return val
