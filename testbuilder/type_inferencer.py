from __future__ import annotations

from functools import reduce
from typing import Mapping, MutableMapping as MMapping, Optional, Sequence, Set, Tuple

import toolz

from dataclasses import dataclass, field

from . import nodetree as n, ssa_basic_blocks as sbb
from .type_store import TypeStore
from .vartypes import AnyType, Type, Types
from .visitor import SimpleVisitor

# We want to do the "right thing". What does that look like?
# First, the "right thing" never creates TypeErrors. So any
# variable which is unrestricted needs to be restricted in order to prevent them.
# Second, the "right thing" uses as many types as possible. So if a function correctly handles arguments of any type, all types will be allowed.


@dataclass
class ModuleTypes:
    functions: Mapping[str, TypeStore]
    code: TypeStore


@dataclass
class InferredType:
    result: Types
    inputs: Sequence[Types] = field(default_factory=list)


class TypeInferencer(SimpleVisitor[TypeStore]):
    def __init__(self) -> None:
        super().__init__()
        self.visit_expr = ExpressionInferencer()

    def visit_Module(self, node: sbb.Module) -> ModuleTypes:
        functions = {name: self.visit(code) for name, code in node.functions.items()}
        code = self.visit(node.code)
        return ModuleTypes(functions=functions, code=code)

    def visit_FunctionDef(self, node: sbb.FunctionDef) -> TypeStore:
        return self.visit(node.blocks)

    def visit_BlockTree(self, node: sbb.BlockTree) -> TypeStore:
        return self.visit(node.end)

    def visit_StartBlock(self, node: sbb.StartBlock) -> TypeStore:
        return TypeStore()

    def visit_ReturnBlock(self, node: sbb.ReturnBlock) -> TypeStore:
        return reduce(lambda x, y: x.merge(y), (self.visit(x) for x in node.parents))

    def visit_Code(self, node: sbb.Code) -> TypeStore:
        store = self.visit(node.parent)
        for line in node.code:
            store = self.visit(line, store)
        return store

    def visit_Conditional(self, node: sbb.Conditional) -> TypeStore:
        true = self.visit(node.true_branch)
        false = self.visit(node.false_branch)
        return TypeStore({}, {})

    def visit_Set(self, node: n.Set, store: TypeStore) -> TypeStore:
        t, store = self.visit_expr(node.e, store)
        name = node.target
        return store.set(name, t)

    def visit_Expr(self, node: n.Expr, store: TypeStore) -> TypeStore:
        self.visit_expr(node.value, store)
        return store


class ExpressionInferencer(SimpleVisitor[Tuple[Types, TypeStore]]):
    def __init__(self) -> None:
        self.visit_op = OpInferencer()

    def visit_Name(self, node: n.Name, store: TypeStore) -> Tuple[Types, TypeStore]:
        return (store.get(node), store)

    def visit_Int(self, node: n.Int, store: TypeStore) -> Tuple[Types, TypeStore]:
        return ({Type.int}, store)

    def visit_BinOp(self, node: n.BinOp, store: TypeStore) -> Tuple[Types, TypeStore]:
        inf_type = self.visit_op(node.op)
        left_type, store = self.visit(node.left, store)
        right_type, store = self.visit(node.right, store)
        if not left_type & inf_type.inputs[0]:
            raise TypeInferenceError()
        if not right_type & inf_type.inputs[1]:
            raise TypeInferenceError()
        return (inf_type.result, store)


class OpInferencer(SimpleVisitor[InferredType]):
    def visit_Lt(self, node: n.Lt) -> InferredType:
        return InferredType(result={Type.boolean}, inputs=[AnyType, AnyType])


class TypeInferenceError(TypeError):
    pass