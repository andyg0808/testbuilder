from abc import abstractmethod
from functools import partial, reduce, singledispatch
from pathlib import Path
from typing import (
    Any,
    Callable,
    Generic,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    TypeVar,
    Union,
    cast,
)

import z3
from dataclasses import dataclass, field

from . import nodetree as n
from .slicing import Dependency
from .visitor import GatherVisitor

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
            lines.append(last_line(b))
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
    line: int


@dataclass
class FalseBranch(Controlled, Parented):
    line: int


@dataclass
class Loop(BasicBlock, Positioned, Parented):
    loops: List[BasicBlock]


@dataclass
class Conditional(BasicBlock, Positioned, Parented):
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

    def deindex(self) -> "BlockTree":
        return BlockTree(start=self.start, end=self.end)

    def unify_return(self, tree: "BlockTree") -> "BlockTree":
        return BlockTree(start=self.start, end=self.end.unify(tree.end))

    def set_target(self, target: T) -> "BlockTreeIndex[T]":
        return BlockTreeIndex.__construct(start=self.start, end=self.end, target=target)


U = TypeVar("U", bound=BasicBlock)


@dataclass
class BlockTreeIndex(BlockTree, Generic[T]):
    __target: T = field(init=False)

    def __post_init__(self) -> None:
        self.__target = cast(T, self.start)

    @staticmethod
    def construct(start: StartBlock, end: ReturnBlock) -> "BlockTreeIndex[StartBlock]":
        return BlockTreeIndex(start=start, end=end)

    @staticmethod
    def __construct(
        start: StartBlock, end: ReturnBlock, target: T
    ) -> "BlockTreeIndex[T]":
        tree: "BlockTreeIndex[T]" = BlockTreeIndex(start=start, end=end)
        tree.__target = target
        return tree

    @property
    def target(self) -> T:
        return self.__target

    def map_target(self, func: Callable[[T], U]) -> "BlockTreeIndex[U]":
        return self.set_target(func(self.target))

    def bind(self, func: Callable[[T], "BlockTreeIndex[U]"]) -> "BlockTreeIndex[U]":
        tree = func(self.target)
        return self.unify_return(tree).set_target(tree.target)

    def map_targets(
        self, func: Callable[..., U], *targets: "BlockTree"
    ) -> "BlockTreeIndex[U]":
        target_trees: List[BlockTree] = [self]
        target_trees += list(targets)
        tree = reduce(lambda acc, val: acc.unify_return(val), target_trees)
        target_list = [t.target for t in target_trees if isinstance(t, BlockTreeIndex)]
        return tree.set_target(func(*target_list))

    def set_target(self, target: U) -> "BlockTreeIndex[U]":
        return BlockTreeIndex.__construct(start=self.start, end=self.end, target=target)

    def return_target(self) -> BlockTree:
        end = self.end.append(self.target)
        return BlockTree(start=self.start, end=end)

    def unify_return(self, tree: BlockTree) -> "BlockTreeIndex[T]":
        return BlockTreeIndex.__construct(
            start=self.start, end=self.end.unify(tree.end), target=self.target
        )


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


def line_range(parent: BasicBlock, end: BasicBlock) -> range:
    """
    Returns the range of line numbers after the end of the parent block,
    but before the end of the end block.
    """
    start_line = last_line(parent)
    end_line = last_line(end)
    return range(start_line + 1, end_line + 1)


def last_line(block: Any) -> int:
    if isinstance(block, BlockTreeIndex):
        return last_line(block.target)
    elif isinstance(block, BlockTree):
        return last_line(block.end)
    elif isinstance(block, ReturnBlock):
        return max(last_line(p) for p in block.parents)
    elif isinstance(block, Positioned) and block.last_line != n.AddedLine:
        return block.last_line
    elif isinstance(block, Parented):
        return last_line(block.parent)
    elif isinstance(block, StartBlock):
        return block.line
    else:
        raise RuntimeError(f"Unexpected end type: {block}")


class LineGatherer(GatherVisitor[int]):
    def visit_Stmt(self, stmt: n.stmt) -> List[int]:
        return [stmt.line]


def lines(block: BasicBlock) -> Set[int]:
    line_list = LineGatherer()(block)
    return set(line_list)
