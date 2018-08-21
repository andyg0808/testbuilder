from typing import List, Mapping, MutableMapping as MMapping, Set, Tuple, TypeVar, Union

from . import nodetree as n, ssa_basic_blocks as sbb
from .visitor import GatherVisitor, UpdateVisitor


class SSARepair(UpdateVisitor):
    def __init__(self, used_vars: Mapping[str, List[int]]) -> None:
        self.used_vars = used_vars

    def visit_Request(self, request: sbb.Request) -> sbb.Request:
        return sbb.Request(module=request.module, code=self.visit(request.code))

    def visit_Name(self, name: n.Name) -> n.Name:
        uselist = self.used_vars[name.id]
        print(f"newcount for {name} is {uselist.index(name.set_count)}")
        return n.Name(id=name.id, set_count=uselist.index(name.set_count))


class VariableVersions(GatherVisitor[Tuple[str, int]]):
    def visit_Name(self, name: n.Name) -> List[Tuple[str, int]]:
        return [(name.id, name.set_count)]


Tree = TypeVar("Tree", bound=Union[sbb.BlockTree, sbb.FunctionDef])


def repair(request: sbb.Request) -> sbb.Request:
    print("repair_request", request)
    used_vars = VariableVersions().visit(request.code)
    varmap: MMapping[str, Set[int]] = {}
    for key, value in used_vars:
        if key in varmap:
            varmap[key].add(value)
        else:
            varmap[key] = {value}

    sorted_vars = {key: sorted(value) for key, value in varmap.items()}
    print("sorted_vars", sorted_vars)
    updated = SSARepair(sorted_vars).visit(request)
    print("updated_request", updated)
    return updated
