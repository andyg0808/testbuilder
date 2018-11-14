from typing import NewType

import z3

ArrayKey = z3.Int
ArrayVal = z3.DatatypeRef
StoreArray = NewType("StoreArray", "z3.ArrayRef[ArrayKey, ArrayVal]")
