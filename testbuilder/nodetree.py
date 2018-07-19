"""
Most of the names in this class are based on the names used in the Python AST.
The visit and generic_visit methods are probably related to their equivalnets
for the Python AST.
"""
from typing import Any, Generic, List, Optional, Sequence, TypeVar, cast

import dataclasses
from dataclasses import dataclass


@dataclass
class Node:
    pass


class stmt(Node):
    pass


class expr(Node):
    pass


@dataclass
class Module(Node):
    body: List[stmt]


@dataclass
class Expr(stmt):
    value: expr


@dataclass
class Int(expr):
    v: int


@dataclass
class Float(expr):
    v: float


@dataclass
class Str(expr):
    s: str


@dataclass
class Operator(Node):
    pass


class Add(Operator):
    pass


class Sub(Operator):
    pass


class Mult(Operator):
    pass


class Div(Operator):
    pass


@dataclass
class CompareOperator(Node):
    pass


class Lt(CompareOperator):
    pass


class LtE(CompareOperator):
    pass


class Gt(CompareOperator):
    pass


class GtE(CompareOperator):
    pass


@dataclass
class UnaryOperator(Node):
    pass


class USub(UnaryOperator):
    pass


@dataclass
class BinOp(expr):
    left: expr
    op: Operator
    right: expr


@dataclass
class UnaryOp(expr):
    op: UnaryOperator
    operand: expr


@dataclass
class Compare(expr):
    left: expr
    op: CompareOperator
    right: expr


@dataclass
class Set(stmt):
    var: "Name"
    e: expr


@dataclass
class Store(expr):
    arr: expr
    idx: int
    value: expr


@dataclass
class BoolOperator(Node):
    pass


class And(BoolOperator):
    pass


class Or(BoolOperator):
    pass


@dataclass
class BoolOp(expr):
    left: expr
    op: BoolOperator
    right: expr


@dataclass
class Return(stmt):
    value: Optional[expr]


@dataclass
class NameConstant(expr):
    value: Any


@dataclass
class Name(expr):
    id: str
    set_count: int


T = TypeVar("T")


class Visitor(Generic[T]):
    def generic_visit(self, node: Node) -> Optional[T]:
        for field in dataclasses.fields(node):
            print(field.type)
            data = getattr(node, field.name)
            if isinstance(data, Sequence):
                map(self.visit, data)
            elif isinstance(data, Node):
                self.visit(data)

        return None

    def visit(self, node: Node) -> Optional[T]:
        name = type(node).__name__
        func = getattr(self, "visit_" + name, self.generic_visit)
        return cast(Optional[T], func(node))
