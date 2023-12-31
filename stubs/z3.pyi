from __future__ import annotations

from fractions import Fraction
from typing import Any, Callable, Generic, List, Tuple, TypeVar, Union, overload


class AstRef:
    pass


class SortRef(AstRef):
    def name(self) -> str:
        ...

    def subsort(self, other: SortRef) -> bool:
        ...

    def __eq__(self, other: object) -> bool:
        ...


T = TypeVar("T", bound=DatatypeRef)


class DatatypeSortRef(SortRef):
    def num_constructors(self) -> int:
        ...

    def recognizer(self, i: int) -> Callable[[ExprRef], BoolRef]:
        ...

    def constructor(self, i: int) -> FuncDeclRef:
        ...

    def accessor(self, i: int, arg: int) -> Callable[[DatatypeRef], ExprRef]:
        ...


class Datatype:
    def __init__(self, name: str) -> None:
        ...

    def declare(self, name: str, *args: Tuple[str, Union[SortRef, Datatype]]) -> None:
        ...

    def create(self) -> DatatypeSortRef:
        ...


class ArraySortRef(SortRef):
    ...


class ArithSortRef(SortRef):
    ...


IntSort = ArithSortRef
RealSort = ArithSortRef
SeqSortRef = ArithSortRef
StringSort = SeqSortRef


class BoolSort(SortRef):
    ...


class ExprRef(AstRef):
    def __eq__(self, other: Any) -> BoolRef:  # type: ignore
        ...

    def __ne__(self, other: Any) -> BoolRef:  # type: ignore
        ...

    def sort(self) -> SortRef:
        ...

    def decl(self) -> FuncDeclRef:
        ...

    def arg(self, idx: int) -> ExprRef:
        ...

    def num_args(self) -> int:
        ...

    def children(self) -> List[ExprRef]:
        ...


class DatatypeRef(ExprRef):
    def decl(self) -> FuncDeclRef:
        ...


def Const(name: str, sort: SortRef) -> ExprRef:
    ...


def Var(idx: int, sort: SortRef) -> ExprRef:
    ...


class CheckSatResult:
    ...


sat: CheckSatResult
unsat: CheckSatResult
unknown: CheckSatResult


class FuncDeclRef:
    def name(self) -> str:
        ...

    def __call__(self, *args: ExprRef) -> ExprRef:
        ...

    def arity(self) -> int:
        ...


class FuncInterp:
    # This isn't quite accurate, but handling the types correctly is too much
    # bother: we'd have to cast all the return values to the types that would
    # have the correct methods.
    def as_long(self) -> int:
        ...

    def as_string(self) -> str:
        ...

    def as_list(self) -> List[Any]:
        ...

    def else_value(self) -> ExprRef:
        ...


class ModelRef:
    def decls(self) -> List[FuncDeclRef]:
        ...

    # This definition is known incomplete; this just gives us the ones we need
    def __getitem__(self, idx: FuncDeclRef) -> Union[FuncInterp, QuantifierRef]:
        ...


class QuantifierRef:
    def is_lambda(self) -> bool:
        ...

    def var_name(self, idx: int) -> str:
        ...

    def var_sort(self, idx: int) -> SortRef:
        ...

    def body(self) -> DatatypeRef:
        ...


class Solver:
    def add(self, *other: ExprRef) -> None:
        ...

    def check(self, *assumptions: ExprRef) -> CheckSatResult:
        ...

    def model(self) -> ModelRef:
        ...

    def reason_unknown(self) -> str:
        ...


class BoolRef(ExprRef):
    ...


def Bool(name: str) -> BoolRef:
    ...


def BoolVal(value: bool) -> BoolRef:
    ...


class ArithRef(ExprRef):
    def __init__(self, name: str) -> None:
        ...


class Int(ArithRef):
    def __mul__(self, other: Int) -> Int:
        ...

    def __add__(self, other: Int) -> Int:
        ...

    @overload
    def __truediv__(self, other: Int) -> Int:
        ...

    @overload
    def __truediv__(self, other: Real) -> Real:
        ...

    @overload
    def __truediv__(self, other: ArithRef) -> Union[Int, Real]:
        ...


class Real(ArithRef):
    def __truediv__(self, other: ArithRef) -> Real:
        ...


class IntVal(Int):
    def __init__(self, value: int) -> None:
        ...


class RatNumRef(Real):
    def __init__(self, value: float) -> None:
        ...

    def as_fraction(self) -> Fraction:
        ...


def RealVal(value: float) -> RatNumRef:
    ...


class SeqRef(ExprRef):
    pass


K = TypeVar("K", bound=ExprRef)
V = TypeVar("V", bound=ExprRef)


class ArrayRef(ExprRef, Generic[K, V]):
    def __getitem__(self, arg: K) -> V:
        ...


class String(SeqRef):
    def __init__(self, name: str) -> None:
        ...


class StringVal(String):
    def __init__(self, value: str) -> None:
        ...


def And(*values: ExprRef) -> BoolRef:
    ...


def Or(*values: ExprRef) -> BoolRef:
    ...


def Not(value: ExprRef) -> BoolRef:
    ...


def is_int(value: Any) -> bool:
    ...


def is_real(value: Any) -> bool:
    ...


def is_bool(value: Any) -> bool:
    ...


def is_string(value: Any) -> bool:
    ...


def is_rational_value(value: Any) -> bool:
    ...


def Length(value: SeqRef) -> Int:
    ...


def eq(a: AstRef, b: AstRef) -> bool:
    ...


E = TypeVar("E", bound=ExprRef)


def simplify(a: E, *args: Any, **kwargs: Any) -> E:
    ...


def Concat(left: String, right: String) -> String:
    ...


def CreateDatatypes(*types: Datatype) -> Tuple[DatatypeSortRef, ...]:
    ...


def ArraySort(key: SortRef, value: SortRef) -> ArraySortRef:
    ...


def Store(array: ArrayRef[K, V], key: K, value: V) -> ArrayRef[K, V]:
    ...


def Array(name: str, key: SortRef, value: SortRef) -> ArrayRef[K, V]:
    ...


def set_param(key: str, value: str) -> None:
    ...


def substitute(expr: ExprRef, *pairs: Tuple[ExprRef, ExprRef]) -> ExprRef:
    ...


DeclareSort = ...  # type: Any


def ToReal(x: Int) -> Real:
    ...
