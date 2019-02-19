from __future__ import annotations

import re
from typing import (
    Any,
    Mapping,
    MutableMapping as MMapping,
    Optional,
    Set,
    Tuple,
    Union,
    cast,
)

Spec = Union[Tuple[int, Any, Any], str]

LeftExpr = re.compile(r"left|first|value|song", re.IGNORECASE)
RightExpr = re.compile(r"right|rest", re.IGNORECASE)


class Pair:
    def __init__(self, left: Any, right: Any):
        self.left = left
        self.right = right

    @staticmethod
    def from_pair(other: Any) -> Optional[Pair]:
        """Attempt to take a foreign pair representation and convert it into
        a `testbuilder.Pair`.

        """

        def _from_pair(other: Any, seen: MMapping[int, Pair]) -> Optional[Pair]:
            key = id(other)
            if key in seen:
                return seen[key]

            left_name = None
            right_name = None
            for n in dir(other):
                if LeftExpr.search(n):
                    left_name = n
                elif RightExpr.search(n):
                    right_name = n
            if left_name and right_name:
                pair = Pair(None, None)
                seen[key] = pair
                pair.left = _from_pair(getattr(other, left_name), seen)
                pair.right = _from_pair(getattr(other, right_name), seen)
                return pair
            else:
                return None

        return _from_pair(other, {})

    @staticmethod
    def pairnet(spec: Spec, globals: Mapping[str, Any] = {}) -> Pair:  # noqa: B006
        """Creates a tree of Pair instances in the format described by the
        supplied `spec`.

        The spec follows this grammar::

            spec ::= (id, spec, spec) | expr
            expr ::= A string to pass to `eval` in order to create the expected value.

        If the `id` of a `spec` has been seen before, its tuple is
        ignored and a reference to the `Pair` created from the
        previous `spec` with that `id` is supplied. This allows
        recursive trees to be described.

        """

        def _pairnet(spec: Spec, known: MMapping[int, Pair]) -> Pair:
            if type(spec) == tuple:
                key, left, right = cast(Tuple[int, Spec, Spec], spec)
                if key in known:
                    return known[key]
                pair = Pair(None, None)
                known[key] = pair
                pair.left = _pairnet(left, known)
                pair.right = _pairnet(right, known)
                return pair
            else:
                return eval(spec, globals)  # type: ignore

        res = _pairnet(spec, {})
        return res

    def __getitem__(self, key: int) -> Any:
        if key == 0:
            return self.left
        if key == 1:
            return self.right
        raise IndexError()

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
        def _eq(self, other: object, matches: MMapping[int, int]) -> bool:
            if not isinstance(other, Pair):
                return False
            if id(self) in matches:
                return id(other) == matches[id(self)]
            else:
                matches[id(self)] = id(other)
            if isinstance(self.left, Pair):
                l_eq = _eq(self.left, other.left, matches)
            else:
                l_eq = self.left == other.left
            if isinstance(self.right, Pair):
                r_eq = _eq(self.right, other.right, matches)
            else:
                r_eq = self.right == other.right
            return bool(l_eq and r_eq)

        res = _eq(self, other, {})
        print("equality", res)
        return res

    def __str__(self) -> str:
        seen = set()

        def _str(self) -> str:
            if id(self) in seen:
                return f"<Pair (recursive {id(self)})>"
            seen.add(id(self))

            if isinstance(self.left, Pair):
                left = _str(self.left)
            else:
                left = str(self.left)
            if isinstance(self.right, Pair):
                right = _str(self.right)
            else:
                right = str(self.right)
            return f"Pair({left}, {right})"

        return _str(self)

    def __repr__(self) -> str:
        pairnet = repr(self.to_pairnet(set()))
        return f"Pair.pairnet({pairnet}, globals=globals())"

    def to_pairnet(self, seen: Optional[Set[int]] = None) -> Spec:
        """This creates a representation of a pair which can be read by the
        `Pair.pairnet` function to recreate the original structure. It
        is able to describe self-referential structures, as well as
        standard tree shapes.

        The format of the representation is described in the
        documentation for the `Pair.pairnet` function.

        """
        if seen is None:
            seen = set()
        if id(self) in seen:
            return (id(self), None, None)
        else:
            seen.add(id(self))
            if isinstance(self.left, Pair):
                left = self.left.to_pairnet(seen)
            else:
                left = repr(self.left)

            if isinstance(self.right, Pair):
                right = self.right.to_pairnet(seen)
            else:
                right = repr(self.right)

            return (id(self), left, right)
