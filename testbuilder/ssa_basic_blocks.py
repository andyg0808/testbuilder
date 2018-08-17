from abc import abstractmethod
from functools import partial, singledispatch
from pathlib import Path
from typing import Any, Callable, Generic, List, Mapping, Optional, Set, TypeVar, Union

from dataclasses import dataclass, field

from . import nodetree as n
from .slicing import Dependency

from




def _default_list() -> Any:
    return field(default_factory=list)


def _no_init() -> Any:
    return field(init=False)


@dataclass
class BasicBlock:
    number: int


@dataclass
class Positioned:
    lines: range


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
        lines = []
        for b in self.parents:
            if isinstance(b, StartBlock):
                lines.append(b.line)
            else:
                lines.append(max(b.lines))
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
class Loop(BasicBlock, Positioned, Parented):
    loop_branch: BasicBlock


@dataclass
class Conditional(BasicBlock, Positioned, Parented):
    true_branch: BasicBlock
    false_branch: BasicBlock


@dataclass
class BlockTree:
    start: StartBlock
    # target: Optional[BasicBlock]
    end: ReturnBlock


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
    code: Union[FunctionDef, BasicBlock]


@dataclass
class TestData:
    filepath: Path
    line: int
    statements: Dependency
    lines: Set[int]
    function_text: str
    function: FunctionDef
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


# E = TypeVar("E", bound=n.expr)


# @dataclass
# class Expr(n.stmt, Generic[E]):
#     value: E
# StopBlock = Optional[BasicBlock]


# @singledispatch
# def last(block: BasicBlock, stop: StopBlock = None) -> BasicBlock:
#     """
#     Returns the last (most ancestral) basic block in a chain of basic
#     blocks.  If `stop` is present, will return its parent block if it
#     is before the end of the chain.
#     """
#     return block


# def parent(
#     block: BasicBlock, stop: StopBlock = None, parent_name: str = "parent"
# ) -> BasicBlock:
#     parent = getattr(block, parent_name)
#     if parent is stop:
#         return block
#     else:
#         return last(parent)


# last.register(Code, parent)
# last.register(TrueBranch, parent)
# last.register(FalseBranch, parent)
# last.register(Loop, partial(parent, parent_name="bypass"))
# last.register(Conditional, partial(parent, parent_name="join"))


# @singledispatch
# def set_parent(
#     target: BasicBlock, block: BasicBlock, parent_name: str = "parent"
# ) -> BasicBlock:
#     raise RuntimeError("Cannot add parent to block without parent-like field")


# BlockCreator = Callable[[BasicBlock], BasicBlock]


# def _set_parent(
#     target: BasicBlock, block: BlockCreator, parent_name: str = "parent"
# ) -> BasicBlock:
#     oldparent = getattr(target, parent_name)
#     newblock = block(oldparent)
#     setattr(target, parent_name, newblock)
#     return newblock


# set_parent.register(Code, set_parent)
# set_parent.register(TrueBranch, set_parent)
# set_parent.register(FalseBranch, set_parent)
# set_parent.register(Loop, partial(set_parent, parent_name="bypass"))
# set_parent.register(Conditional, partial(set_parent, parent_name="join"))


# def insert(blocks: BasicBlock, block: BlockCreator, point: StopBlock) -> BasicBlock:
#     if blocks is point:
#         return block(blocks)
#     node = parent(blocks, point)
#     set_parent(node, block)
#     return blocks
