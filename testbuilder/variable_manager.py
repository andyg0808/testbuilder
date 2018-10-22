from copy import copy
from typing import List, MutableMapping as MMapping, Optional

VarMapping = MMapping[str, int]
VAR_START_VALUE = 0


class VariableManager:
    def __init__(self, variables: Optional[VarMapping] = None) -> None:
        if variables is None:
            variables = {}
        self.stack: List[VarMapping] = []
        self.variables = variables

    def get(self, name: str) -> int:
        set_count = self.variables.get(name, VAR_START_VALUE)
        if name not in self.variables:
            self.variables[name] = set_count
        return set_count

    def get_target(self, name: str) -> int:
        set_count = self.variables.get(name, VAR_START_VALUE)
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
        self.variables = copy(self.stack[-1])

    def mapping(self) -> VarMapping:
        return copy(self.variables)

    def update(self, mapping: VarMapping) -> None:
        self.variables = mapping

    def __repr__(self) -> str:
        return f"<VariableManager variables={self.variables}, stack={self.stack}>"
