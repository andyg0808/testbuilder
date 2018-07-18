import ast
from typing import Any, List, Optional, Set, Union

from .ast_formatter import format_tree
from .slicing import Dependency, NegConditional


class _BlockType:
    def __repr__(self) -> str:
        return str(self.__class__.__name__)


class _Loop(_BlockType):
    pass


class _Conditional(_BlockType):
    pass


class _Code(_BlockType):
    pass


Loop = _Loop()
Conditional = _Conditional()
Code = _Code()


BlockType = _BlockType


class BasicBlock:
    """
    Attributes:
        conditional: A conditional controlling this basic block
        children: Child blocks
        parents: Parent blocks
        code: The code in this basic block (not including the conditional)
        join: If this basic block is controlled by a conditional, this is the
        block at which the conditional no longer controls. (I.e.: for an if
        statement, this is the block at which the true and false blocks join;
        for a while loop, this is the child block which is not pointing back up.)
        returns: True if a node at this level of the AST contains a return.
    """

    def __init__(self, number: int = -1) -> None:
        self.conditional: Optional[Dependency] = None
        self.children: List[BasicBlock] = []
        self.parents: List[BasicBlock] = []
        self.code: List[Dependency] = []
        self.join: Optional[BasicBlock] = None
        self.type: BlockType = Code
        self.required = False
        self.number = number
        self.returns = False

    # This is too cute by half, but... self gets added to the parents array
    # when this is called as a method. So it includes self as a parent block on
    # the new child.
    def start_block(*parents: "BasicBlock") -> "BasicBlock":
        """
        Creates a new block as a child of this block. If you need to add
        parents to the new block, add arguments. If you need more children of a
        block, call this multiple times.

        parents  Pass additional blocks to assign as parent blocks.
        """
        new_block: BasicBlock = BasicBlock()
        new_block.number = sum(b.number for b in parents) + 1
        for block in parents:
            new_block.parents.append(block)
            block.children.append(new_block)
        return new_block

    # This is too cute by half, but... self gets added to the parents array
    # when this is called as a method. So it includes self as a parent block on
    # the new child.
    def start_parent(*children: "BasicBlock") -> "BasicBlock":
        """
        Creates a new block as a parent of this block. If you need to add
        children to the new block, add arguments. If you need more parents of a
        block, call this multiple times.

        @param children  Pass additional blocks to assign as parent blocks.
        """
        new_block: BasicBlock = BasicBlock()
        new_block.number = sum(b.number for b in children) + 1
        for block in children:
            new_block.children.append(block)
            block.parents.append(new_block)
        return new_block

    def append(self, code: Dependency) -> None:
        self.code.append(code)

    def trace_blocks(self) -> Any:
        seen = set([self])
        return (
            [p.trace_parents(seen) for p in self.parents if p is not self]
            + [self]
            + [p.trace_children(seen) for p in self.children if p is not self]
        )

    def trace_parents(self, seen: Set[Any]) -> Any:
        if self in seen:
            return []
        else:
            seen.add(self)
        return [self] + [p.trace_parents(seen) for p in self.parents if p is not self]

    def trace_children(self, seen: Set[Any]) -> Any:
        if self in seen:
            return []
        else:
            seen.add(self)
        return [self] + [p.trace_children(seen) for p in self.children if p is not self]

    def __repr__(self) -> str:
        if self.conditional:
            return "BasicBlock({} <> {})".format(
                format_tree(self.conditional.code),
                "\uf063".join(format_tree(c.code) for c in self.code),
            )
        else:
            return "BasicBlock({})".format(
                ";".join(format_tree(c.code) for c in self.code)
            )

    def _get_label(self) -> str:
        body = "\n".join(format_tree(c.code) for c in self.code)
        if self.conditional:
            conditional = format_tree(self.conditional.code)
            if isinstance(self.conditional, NegConditional):
                conditional = "!({})".format(conditional)
            return "{}:\n{}".format(conditional, body)
        else:
            return body

    def dot(self, done: Optional[Set[Any]] = None) -> List[str]:
        if not done:
            done = set()

        output: List[str] = []
        if self in done:
            return output
        output.append(
            '{}[label="{}",xlabel="{}"];'.format(
                id(self), self._get_label(), self.number
            )
        )
        # output.append("{} -> {} [arrowhead=none];".format(self.number, id(self)))
        # output.append('{}[label="{}", shape=none];'.format(self.number, self.number))
        done.add(self)
        for child in self.children:
            output += child.dot(done)
            link = "{} -> {};".format(id(self), id(child))
            if link not in done:
                output.append(link)
                done.add(link)
        for parent in self.parents:
            output += parent.dot(done)
            link = "{} -> {};".format(id(parent), id(self))
            if link not in done:
                output.append(link)
                done.add(link)

        return output
