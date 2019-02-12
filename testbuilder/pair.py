from __future__ import annotations

from typing import Any, Set


class Pair:
    def __init__(self, left: Any, right: Any):
        self.left = left
        self.right = right

    @property
    def first(self):  # type: ignore
        return self.left

    @property
    def second(self):  # type: ignore
        return self.right

    @property
    def rest(self):  # type: ignore
        return self.right

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Pair):
            return False
        l_eq = self.left == other.left
        r_eq = self.right == other.right
        return bool(l_eq and r_eq)

    def __repr__(self) -> str:
        return self.__repr_helper(set())

    def __repr_helper(self, seen: Set[int]) -> str:
        if id(self) in seen:
            return f"<Pair {id(self)}>"
        else:
            seen.add(id(self))
            if isinstance(self.left, Pair):
                left = self.left.__repr_helper(seen)
            else:
                left = repr(self.left)

            if isinstance(self.right, Pair):
                right = self.right.__repr_helper(seen)
            else:
                right = repr(self.right)

            ret: str = ("Pair(" + left + ", " + right + ")")
            return ret
