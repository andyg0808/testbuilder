import ast
from copy import copy
from dataclasses import dataclass, field
from functools import reduce, singledispatch
from pathlib import Path
from typing import Any, Callable, Generic, List, Mapping, Set, TypeVar, Union, cast

import z3
from visitor import SetGatherVisitor

from . import nodetree as n

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

    def append(self, item: BasicBlock) -> "ReturnBlock":
        if id(item) in self.__parent_ids():
            parents = copy(self.parents)
        else:
            parents = self.parents + [item]
        return ReturnBlock(number=self.number, parents=parents)

    def __parent_ids(self) -> Set[int]:
        return {id(x) for x in self.parents}

    def unify(self, other: "ReturnBlock") -> "ReturnBlock":
        parents = copy(self.parents)
        ids = self.__parent_ids()
        for p in other.parents:
            if id(p) not in ids:
                parents.append(p)
        return ReturnBlock(number=self.number, parents=parents)

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
    line: int


@dataclass
class TrueBranch(Controlled, Parented):
    pass


@dataclass
class ForcedTrueBranch(TrueBranch):
    """Represents a `TrueBranch` which causes an exit when taken (e.g., a
    branch of an `if` with a `return` at the bottom.
    """

    pass


@dataclass
class FalseBranch(Controlled, Parented):
    pass


@dataclass
class ForcedFalseBranch(FalseBranch):
    """Represents a `FalseBranch` which causes an exit when taken (e.g., a
    branch of an `if` with a `return` at the bottom.

    """

    pass


@dataclass
class WhileFalseBranch(FalseBranch):
    controlled_line: int


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
    """Stores a tree of SSA basic blocks. Keeps a pointer to the top
    block (the `StartBlock`) as well as the final block (the
    `ReturnBlock`).

    """

    start: StartBlock
    end: ReturnBlock

    def empty(self) -> bool:
        """Returns true if the tree does not contain any blocks besides the
        start and return blocks.

        """
        if len(self.end.parents) == 0:
            return True
        if len(self.end.parents) == 1 and self.start is self.end.parents[0]:
            return True
        return False

    def deindex(self) -> "BlockTree":
        """Return a basic BlockTree, throwing out any subclass data.

        """
        return BlockTree(start=self.start, end=self.end)

    def unify_return(self, tree: "BlockTree") -> "BlockTree":
        """Combines two BlockTrees by taking the union of the parents from
        their respective ReturnBlocks.

        """
        return BlockTree(start=self.start, end=self.end.unify(tree.end))

    def set_target(self, target: T) -> "BlockTreeIndex[T]":
        return BlockTreeIndex._construct(start=self.start, end=self.end, target=target)


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
    def _construct(
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
        return BlockTreeIndex._construct(start=self.start, end=self.end, target=target)

    def return_target(self) -> BlockTree:
        """
        Appends the current target of the index to the end block and
        returns a BlockTree (since there's no longer a target
        available)
        """
        end = self.end.append(self.target)
        return BlockTree(start=self.start, end=end)

    def unify_return(self, tree: BlockTree) -> "BlockTreeIndex[T]":
        return BlockTreeIndex._construct(
            start=self.start, end=self.end.unify(tree.end), target=self.target
        )


@dataclass
class FunctionDef(Positioned):
    name: str
    args: List[str]
    blocks: BlockTree
    defaults: List[n.expr]
    original: ast.FunctionDef


@dataclass
class ClassDef(Positioned):
    name: str
    variables: List[str]
    functions: List[FunctionDef]


@dataclass
class Module:
    functions: Mapping[str, FunctionDef]
    classes: Mapping[str, ClassDef]
    code: BlockTree


@dataclass
class Request:
    module: Module
    code: Union[FunctionDef, BlockTree]


@dataclass(frozen=True)
class Variable:
    id: str


@dataclass
class TestData:
    # line: int
    # statements: Dependency
    # lines: Set[int]
    # function: Optional[FunctionDef] = None
    name: str
    source_text: str
    free_variables: List[Variable]
    expression: Expression
    filepath: Path


Solution = Mapping[str, Any]


@dataclass
class SolvedTestData(TestData):
    test_number: int
    target_line: int
    args: Solution


@dataclass
class ExpectedTestData(SolvedTestData):
    expected_result: str


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
    if isinstance(block, Module):
        candidates: List[int] = []
        candidates += [last_line(f) for f in block.functions.values()]
        candidates += [last_line(c) for c in block.classes.values()]
        candidates.append(last_line(block.code))
        return max(candidates)
    elif isinstance(block, BlockTreeIndex):
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
        raise RuntimeError(f"Unexpected end type: {type(block)}")


class LineGatherer(SetGatherVisitor[int]):
    def visit_Stmt(self, stmt: n.stmt) -> Set[int]:
        return {stmt.line}


def lines(block: BasicBlock) -> Set[int]:
    line_list = LineGatherer()(block)
    return set(line_list)
