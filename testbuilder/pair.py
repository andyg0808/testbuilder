from __future__ import annotations

from typing import Any, MutableMapping as MMapping, Optional, Set, Tuple, Union, cast

Spec = Union[Tuple[int, Any, Any], str]


class Pair:
    def __init__(self, left: Any, right: Any):
        self.left = left
        self.right = right

    @staticmethod
    def pairnet(spec: Spec) -> Pair:
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
                return eval(spec)  # type: ignore

        return _pairnet(spec, {})

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
        if not isinstance(other, Pair):
            return False
        l_eq = self.left == other.left
        r_eq = self.right == other.right
        return bool(l_eq and r_eq)

    def __repr__(self) -> str:
        pairnet = repr(self.to_pairnet(set()))
        return f"Pair.pairnet({pairnet})"

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
