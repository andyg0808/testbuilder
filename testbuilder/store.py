from typing import MutableMapping as MMapping

import z3
from dataclasses import dataclass, field

from .z3_types import PairT


@dataclass(frozen=True)
class Reference:
    pass


@dataclass
class Store:
    values: MMapping[Reference, PairT] = field(default_factory=dict)
