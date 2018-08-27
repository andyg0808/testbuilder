from typing import Optional, List
from copy import copy
from .ast_builder import VAR_START_VALUE
from .expression_builder import VarMapping

class VariableManager:
    def __init__(self, variables: Optional[VarMapping]=None) -> None:
        if variables is None:
            variables = {}
        self.stack: List[VarMapping] = []
        self.variables = variables

    def get(self, name: str) -> int:
        return self.variables.get(name, VAR_START_VALUE)

    def get_target(self, name: str) -> int:
        set_count = self.get(name)
        if name in self.variables:
            set_count += 1
        self.variables[name] = set_count
        return set_count


    def push(self) -> None:
        self.stack.append(copy(self.variables))

    def pop(self) -> None:
        self.variables = self.stack.pop()

    def refresh(self) -> None:
        self.variables = self.stack[-1]

    def mapping(self) -> VarMapping:
        return copy(self.variables)

    def update(self, mapping: VarMapping) -> None:
        self.variables = mapping
