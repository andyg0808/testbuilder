import ast
from typing import List, Mapping, MutableMapping as MMapping, Optional, Sequence, Set

from . import basic_block
from .basic_block import BasicBlock, BlockTree, BlockType
from .slicing import Conditional, Dependency, Statement


def make_display(k: int) -> str:
    return str(k % 10000)


RETURNBLOCK = 0
STARTBLOCK = 1

NodeOrdering = MMapping[int, List[Optional[int]]]


class TreeWalker(ast.NodeVisitor):
    def __init__(self, code: ast.AST) -> None:
        super().__init__()
        self.tree: MMapping[int, List[int]] = {STARTBLOCK: [], RETURNBLOCK: []}
        self.mapping: MMapping[int, int] = {}
        self.current_block: int = STARTBLOCK
        self.last_block = self.current_block
        self.types: MMapping[int, BlockType] = {}
        self.returns: MMapping[int, bool] = {}
        self.control: List[int] = []
        self.node_order: NodeOrdering = {}
        self.code = code

    def get_builder(self) -> "TreeBuilder":
        return TreeBuilder(
            mapping=self.mapping,
            tree=self.tree,
            types=self.types,
            returns=self.returns,
            node_order=self.node_order,
            code=self.code,
        )

    def create_block(self, parent: Optional[int] = None) -> int:
        """
        Creates a new block and attaches it to a parent block.
        Args:
            parent: If present, sets the parent block for the new block. If not
                    present, the current block will be used.
        """
        if not parent:
            parent = self.current_block
        self.last_block += 1
        self.attach(parent, self.last_block)
        self.current_block = self.last_block
        self.tree[self.current_block] = []
        return self.current_block

    def attach(self, start: int, end: Optional[int] = None) -> None:
        """
        If only one argument is provided, it is used as the child block and the
        current block is used as the parent. If two arguments are provided, the
        first is used as the parent block and the second is used as the child.
        """
        if end is None:
            end = start
            start = self.current_block
        self.tree[start].append(end)

    def visit_If(self, node: ast.If) -> bool:
        start_block = self.create_block()
        self.types[start_block] = basic_block.StartConditional
        self.visit(node.test)

        # True branch
        self.create_block()
        self.control.append(self.current_block)
        join: Optional[int] = None
        true_branch: Optional[int]
        if not self.visit_body(node.body):
            true_branch = self.current_block
            join = self.create_block()
        else:
            true_branch = None
        self.control.pop()

        # False branch
        self.create_block(start_block)
        self.control.append(self.current_block)
        false_branch: Optional[int]
        if not self.visit_body(node.orelse):
            false_branch = self.current_block
            if join:
                self.attach(join)
            else:
                join = self.create_block()
        elif not join:
            # Both branches of the if had returns. That makes it a
            # return statement, in effect. Returning True indicates
            # that all control flow ends at this block.
            return True
        else:
            false_branch = None
        self.control.pop()

        # Add join as a third child to start_block. This eliminates the need to
        # figure out which block is the join point to determine when the
        # conditional ends.
        self.attach(start_block, join)

        self.current_block = join
        self.types[join] = basic_block.Conditional
        self.node_order[join] = [true_branch, false_branch, start_block]
        self.create_block()
        return False

    def visit_body(self, body: Sequence[ast.AST]) -> bool:
        """
        Stops processing if `body` contains a return.
        Returns true when this occurs.
        """
        for n in body:
            if self.visit(n):
                return True
        return False

    def visit_While(self, node: ast.While) -> None:
        parent = self.current_block
        start_block = self.create_block()
        self.visit(node.test)
        self.types[start_block] = basic_block.Loop
        # Create body block
        self.create_block()
        self.control.append(self.current_block)
        body = None
        if not self.visit_body(node.body):
            self.attach(self.current_block, start_block)
            body = self.current_block
        self.control.pop()
        # Create next block
        self.current_block = start_block
        self.create_block()
        self.node_order[start_block] = [body, parent]

    def visit_Return(self, node: ast.Return) -> bool:
        self.attach(RETURNBLOCK)
        if self.control:
            control = self.control[-1]
            self.returns[control] = True
        self.generic_visit(node)
        return True

    def generic_visit(self, node: ast.AST) -> None:
        self.mapping[id(node)] = self.current_block
        super().generic_visit(node)


class TreeBuilder:
    def __init__(
        self,
        mapping: Mapping[int, int],
        tree: Mapping[int, Sequence[int]],
        types: Mapping[int, BlockType],
        returns: Mapping[int, bool],
        node_order: NodeOrdering,
        code: ast.AST,
    ) -> None:
        self.mapping = mapping
        self.tree = tree
        self.types = types
        self.returns = returns
        self.node_order = node_order
        self.code = code

    def _is_ancestor(
        self, ancestor: BasicBlock, current: BasicBlock, seen: Set[BasicBlock]
    ) -> bool:
        if ancestor is current:
            return True

        if current in seen:
            return False

        seen.add(current)

        return any(
            self._is_ancestor(ancestor, c, seen)
            for c in current.parents
            if c is not None
        )

    def get_block(
        self, block_num: int, parent: Optional[BasicBlock] = None
    ) -> BasicBlock:
        if parent:
            block = parent.start_block()
        else:
            block = BasicBlock()
        block.number = block_num
        block.type = self.types.get(block_num, basic_block.Code)
        block.returns = self.returns.get(block_num, False)
        return block

    def build_tree(self) -> Mapping[int, BasicBlock]:
        blocks: MMapping[int, BasicBlock] = {}
        for p, cs in self.tree.items():
            if p not in blocks:
                parent = self.get_block(p)
                blocks[p] = parent
            else:
                parent = blocks[p]
            for c in cs:
                if c not in blocks:
                    blocks[c] = self.get_block(c, parent)
                else:
                    child = blocks[c]
                    if parent not in child.parents:
                        child.parents.append(parent)
                    if child not in parent.children:
                        parent.children.append(child)
                    # print("parent vs child", parent, child, p, c)

        self.order_blocks(blocks)
        return blocks

    def dot(self) -> List[str]:
        data = []
        for k, vs in self.tree.items():
            for v in vs:
                data.append("{} -> {};".format(k, v))
        return data

    def _inflate_deps(self, s: Dependency, blocks: Mapping[int, BasicBlock]) -> None:
        for dep in s.dependencies:
            if type(dep) is Statement:
                self._inflate(dep, blocks)
            elif isinstance(dep, Conditional):
                self._inflate_conditional(dep, blocks)

    def _fetch_block(
        self, code: ast.AST, blocks: Mapping[int, BasicBlock]
    ) -> BasicBlock:
        code_id = id(code)
        block_id = self.mapping[code_id]
        block = blocks[block_id]
        return block

    def _inflate(self, s: Dependency, blocks: Mapping[int, BasicBlock]) -> BasicBlock:
        self._inflate_deps(s, blocks)
        block = self._fetch_block(s.code, blocks)
        if s not in block.code:
            block.append(s)
        if s.required:
            block.required = True
        return block

    def _set_conditionals(self, block: BasicBlock, cond: Conditional) -> None:
        if block.conditional:
            assert block.conditional.code == cond.code
        else:
            block.conditional = cond

    def _inflate_conditional(
        self, s: Conditional, blocks: Mapping[int, BasicBlock]
    ) -> None:
        self._inflate_deps(s, blocks)
        assert isinstance(s.code, ast.Expr)
        block = self._fetch_block(s.code.value, blocks)
        if s.required:
            block.required = True

        if type(s) is Conditional:
            self._set_conditionals(block, s)
        else:
            self._set_conditionals(block, s.neg())

    def order_blocks(self, blocks: Mapping[int, BasicBlock]) -> None:
        for k, vs in self.node_order.items():
            parents = [blocks[i] if i is not None else None for i in vs]
            blocks[k].parents = parents

    def inflate(self, s: Dependency) -> BlockTree:
        blocks = self.build_tree()
        target = self._inflate(s, blocks)
        for block in blocks.values():
            block.code.sort(key=lambda x: x.lineno)
        return BlockTree(blocks[STARTBLOCK], target, blocks[RETURNBLOCK], self.code)


def build_tree(syntax_tree: ast.AST) -> TreeBuilder:
    walker = TreeWalker(syntax_tree)
    walker.visit(syntax_tree)
    return walker.get_builder()
