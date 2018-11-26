from typing import NewType

import z3

from .z3_types import ReferenceT

ArrayKey = ReferenceT
ArrayVal = z3.DatatypeRef
StoreArray = NewType("StoreArray", "z3.ArrayRef[ArrayKey, ArrayVal]")
