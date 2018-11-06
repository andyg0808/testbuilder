from enum import Enum
from typing import Set

Type = Enum("Type", "int boolean")
Types = Set[Type]

# The set of all types
AnyType = set(Type)
