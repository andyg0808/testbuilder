from copy import copy
from typing import List, Optional

from .ast_builder import VAR_START_VALUE
from .expression_builder import VarMapping


class VariableManager:
    def __init__(self, variables: Optional[VarMapping] = None) -> None:
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

    def add(self, varlist: List[str]) -> None:
        """
        Initialize variables in varlist to new indices, as though they
        have just been set. This is useful for adding arguments to the
        list of variables.
        """
        for var in varlist:
            # It's as though each of these variables has been assigned
            # to already.
            self.get_target(var)

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
