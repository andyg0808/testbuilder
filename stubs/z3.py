from typing import Any, List, Tuple


class AstRef:
    pass


class SortRef(AstRef):
    def name(self) -> str:
        ...


class DatatypeSortRef(SortRef):
    ...


class Datatype:
    def __init__(self, name: str) -> None:
        ...

    def declare(self, name: str, *args: Tuple[str, SortRef]) -> None:
        ...

    def create(self) -> DatatypeSortRef:
        ...


class ArithSortRef(SortRef):
    ...


IntSort = ArithSortRef


class BoolSort(SortRef):
    ...


class ExprRef(AstRef):
    def __eq__(self, other: Any) -> "ExprRef":  # type: ignore
        ...

    def sort(self) -> SortRef:
        ...


class DatatypeRef(ExprRef):
    def decl(self) -> FuncDeclRef:
        ...


def Const(name: str, sort: SortRef) -> ExprRef:
    ...


class CheckSatResult:
    ...


sat: CheckSatResult
unsat: CheckSatResult
unknown: CheckSatResult


class FuncDeclRef:
    def name(self) -> str:
        ...


class FuncInterp:
    # This isn't quite accurate, but handling the types correctly is too much
    # bother: we'd have to cast all the return values to the types that would
    # have the correct methods.
    def as_long(self) -> int:
        ...

    def as_string(self) -> str:
        ...


class ModelRef:
    def decls(self) -> List[FuncDeclRef]:
        ...

    # This definition is known incomplete; this just gives us the ones we need
    def __getitem__(self, idx: FuncDeclRef) -> FuncInterp:
        ...


class Solver:
    def add(self, *other: ExprRef) -> None:
        ...

    def check(self, *assumptions: ExprRef) -> CheckSatResult:
        ...

    def model(self) -> ModelRef:
        ...


class Bool(ExprRef):
    def __init__(self, name: str) -> None:
        ...


class BoolVal(Bool):
    def __init__(self, value: bool) -> None:
        ...


class Int(ExprRef):
    def __init__(self, name: str) -> None:
        ...

    def __mul__(self, other: Int) -> Int:
        ...


class IntVal(Int):
    def __init__(self, value: int) -> None:
        ...


class SeqRef(ExprRef):
    pass


class String(SeqRef):
    def __init__(self, name: str) -> None:
        ...


class StringVal(SeqRef):
    def __init__(self, value: str) -> None:
        ...


def And(*values: ExprRef) -> ExprRef:
    ...


def Or(*values: ExprRef) -> ExprRef:
    ...


def Not(value: ExprRef) -> ExprRef:
    ...


def is_int(value: Any) -> bool:
    ...


def is_bool(value: Any) -> bool:
    ...


def is_string(value: Any) -> bool:
    ...


def eq(a: AstRef, b: AstRef) -> bool:
    ...


def simplify(a: ExprRef, *args: Any, **kwargs: Any) -> ExprRef:
    ...


DeclareSort = ...  # type: Any
