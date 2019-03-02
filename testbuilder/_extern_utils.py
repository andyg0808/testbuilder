import re
from typing import Any

from .pair import Pair

PairExpr = re.compile(r"pair", re.IGNORECASE)
ListExpr = re.compile(r"List")


def convert_result(val: Any) -> Any:
    """
    If possible, convert a value to a known type from whatever type it was.
    """
    name = type(val).__name__
    if PairExpr.search(name) or ListExpr.search(name):
        pair = Pair.from_pair(val)
        if pair is not None:
            return pair
    elif isinstance(val, tuple):
        return tuple(convert_result(v) for v in val)
    return val
