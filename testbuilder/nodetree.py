"""
Most of the names in this class are based on the names used in the Python AST.
The visit and generic_visit methods are potentially based on the equivalent
functions for the Python AST.
"""
from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from typing import Any, Generic, List, Optional, Sequence, Tuple, TypeVar

AddedLine = -1


@dataclass
class Node:
    pass


@dataclass
class stmt(Node):
    line: int


class expr(Node):
    pass


@dataclass
class Body(Node):
    """
    A body is a list of statements which are executed in sequence.
    """

    body: List[stmt]


E = TypeVar("E", bound=expr)


@dataclass
class Expr(stmt, Generic[E]):
    value: E


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


class NotEq(Operator):
    pass


@dataclass
class UnaryOperator(Node):
    pass


class USub(UnaryOperator):
    pass


class Not(UnaryOperator):
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
    target: LValue
    e: expr


@dataclass
class PhiSet(Set):
    pass


@dataclass
class ArgumentBind(Set):
    target: PrefixedName
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


class LValue:
    @abstractmethod
    def find_name(self) -> Name:
        ...


@dataclass
class Attribute(expr, LValue):
    value: LValue
    attr: str

    def find_name(self) -> Name:
        return self.value.find_name()


@dataclass
class Name(expr, LValue):
    id: str
    set_count: int

    def find_name(self) -> Name:
        return self

    def __post_init__(self) -> None:
        assert isinstance(self.id, str)
        assert isinstance(self.set_count, int)


@dataclass
class Prefix:
    func: str
    number: int


@dataclass
class PrefixedName(Name, Prefix):
    pass


@dataclass
class Result(expr, Prefix):
    pass


@dataclass
class ReturnResult(stmt, Prefix):
    value: Optional[expr]


@dataclass
class Call(expr):
    func: expr
    args: Sequence[expr]
    keywords: Sequence[Tuple[str, expr]]
