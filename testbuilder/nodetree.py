"""
Most of the names in this class are based on the names used in the Python AST.
The visit and generic_visit methods are potentially based on the equivalent
functions for the Python AST.
"""
from typing import Any, Generic, List, Optional, Sequence, Tuple, TypeVar, cast

import dataclasses
from dataclasses import dataclass

from .visitor import Visitable


@dataclass
class Node(Visitable):
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


class Lt(Operator):
    pass


class LtE(Operator):
    pass


class Gt(Operator):
    pass


class GtE(Operator):
    pass


class Eq(Operator):
    pass


@dataclass
class UnaryOperator(Node):
    pass


class USub(Operator):
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
class Set(stmt):
    target: "Name"
    e: expr


@dataclass
class Store(expr):
    arr: expr
    idx: int
    value: expr


class And(Operator):
    pass


class Or(Operator):
    pass


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


@dataclass
class Call(expr):
    func: expr
    args: Sequence[expr]
    keywords: Sequence[Tuple[str, expr]]


# T = TypeVar("T")


# class Visitor:
#     def generic_visit(self, node: Node) -> Any:
#         for field in dataclasses.fields(node):
#             print(field.type)
#             data = getattr(node, field.name)
#             if isinstance(data, Sequence):
#                 map(self.visit, data)
#             elif isinstance(data, Node):
#                 self.visit(data)

#         return None

#     def visit(self, node: Node) -> Any:
#         name = type(node).__name__
#         func = getattr(self, "visit_" + name, self.generic_visit)
#         return cast(Optional[T], func(node))
