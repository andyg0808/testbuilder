from abc import abstractmethod
from functools import partial, singledispatch
from pathlib import Path
from typing import Any, Callable, Generic, List, Mapping, Optional, Set, TypeVar, Union

import z3
from dataclasses import dataclass, field

from . import nodetree as n
from .slicing import Dependency

Expression = z3.ExprRef


def _default_list() -> Any:
    return field(default_factory=list)


def _no_init() -> Any:
    return field(init=False)


@dataclass
class BasicBlock:
    number: int


@dataclass
class Positioned:
    first_line: int
    last_line: int

    @property
    def lines(self) -> range:
        return range(self.first_line, self.last_line + 1)


@dataclass
class Parented:
    parent: BasicBlock


@dataclass
class ReturnBlock(BasicBlock):
    parents: List[BasicBlock] = _default_list()

    def append(self, item: BasicBlock) -> None:
        self.parents.append(item)

    @property
    def line(self) -> int:
        if not self.parents:
            raise RuntimeError("Should have at least one parent of a ReturnBlock")
        lines = []
        for b in self.parents:
            if isinstance(b, Positioned):
                lines.append(max(b.lines))
            elif isinstance(b, StartBlock):
                lines.append(b.line)
        return max(lines)


@dataclass
class Code(BasicBlock, Positioned, Parented):
    code: List[n.stmt]

    def append(self, item: n.stmt) -> None:
        self.code.append(item)


@dataclass
class StartBlock(BasicBlock):
    line: int


@dataclass
class Controlled(BasicBlock):
    conditional: n.expr


@dataclass
class TrueBranch(Controlled, Parented):
    pass


@dataclass
class FalseBranch(Controlled, Parented):
    pass


@dataclass
class Loop(Controlled, Positioned, Parented):
    loops: List[BasicBlock]


@dataclass
class Conditional(Controlled, Positioned, Parented):
    true_branch: BasicBlock
    false_branch: BasicBlock


class TreeTail:
    pass


T = TypeVar("T", bound=BasicBlock)


@dataclass
class BlockTree:
    start: StartBlock
    end: ReturnBlock

    def empty(self) -> bool:
        if len(self.end.parents) == 0:
            return True
        if len(self.end.parents) == 1 and self.start is self.end.parents[0]:
            return True
        return False


@dataclass
class BlockTreeIndex(BlockTree, Generic[T]):
    target: T

    def set_target(self, target: T) -> "BlockTreeIndex[T]":
        return BlockTreeIndex(start=self.start, end=self.end, target=target)


@dataclass
class FunctionDef(Positioned):
    name: str
    args: List[str]
    blocks: BlockTree


@dataclass
class Module:
    functions: Mapping[str, FunctionDef]
    code: BlockTree


@dataclass
class Request:
    module: Module
    code: Union[FunctionDef, BlockTree]


@dataclass
class Variable:
    id: str


@dataclass
class TestData:
    # filepath: Path
    # line: int
    name: str
    # statements: Dependency
    # lines: Set[int]
    # function_text: str
    # function: Optional[FunctionDef] = None
    free_variables: List[Variable]
    expression: Expression


@singledispatch
def dump_tree(block: BasicBlock, depth: int = 0) -> None:
    print(" " * depth, block)


@dump_tree.register(Parented)
def dump_Parented(block: Parented, depth: int = 0) -> None:
    print(" " * depth, block)
    dump_tree(block.parent, depth + 1)


@dump_tree.register(ReturnBlock)
def dump_ReturnBlock(block: ReturnBlock, depth: int = 0) -> None:
    print(" " * depth, block)
    for parent in block.parents:
        dump_tree(parent, depth + 1)
