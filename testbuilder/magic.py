from __future__ import annotations

import inspect
from itertools import product
from typing import (
    Callable,
    Iterator,
    List,
    Optional,
    Sequence,
    Tuple,
    Type,
    TypeVar,
    Union,
    cast,
)

from logbook import Logger
from toolz import concat

import z3
from dataclasses import dataclass

from .constrained_expression import ConstrainedExpression as CExpr
from .type_union import TypeUnion
from .variable_type_union import VariableTypeUnion
from .z3_types import Expression

log = Logger("Magic")


T = TypeVar("T")

MagicFunc = Callable[..., T]
TagType = Union[z3.SortRef, Type]


@dataclass(frozen=True)
class MagicTag:
    types: Sequence[TagType]


def magic_tag(*types: TagType) -> Callable[[MagicFunc], MagicFunc]:
    def _magic(func: MagicFunc) -> MagicFunc:
        setattr(func, "__magic", MagicTag(types=types))
        return func

    return _magic


@dataclass(frozen=True)
class MagicRegistration(MagicTag):
    function: MagicFunc


class Magic:
    """
    Function overloading and abstract type handling.

    A `Magic` is a callable object which accepts any number of
    `TypeUnion`s as arguments. It searches for registered handler
    functions for each element of the Cartesian product of all the
    expressions in each `TypeUnion`. It discards those n-tuples of
    types which do not have defined handlers. For those which do have
    handlers, it calls the handler with the expressions from the
    n-tuple.

    """

    def __init__(self) -> None:
        self.funcref: List[MagicRegistration] = []
        for _, method in inspect.getmembers(self, inspect.ismethod):
            magic = getattr(method, "__magic", None)
            if magic is not None:
                registration = MagicRegistration(function=method, types=magic.types)
                self.funcref.append(registration)

    @staticmethod
    def m(*types: TagType) -> Callable[[MagicFunc], MagicFunc]:
        """
        Create an instance of Magic and call `magic` on it with these
        arguments.
        """
        res = Magic()
        return res.magic(*types)

    def magic(self, *types: TagType) -> Callable[[MagicFunc], Magic]:
        """
        To register an existing function for some argument types, call
        this method, passing it the argument types, and pass the
        existing function to the returned registration function. The
        registration function returns the original Magic object,
        so calls can be chained.

        Arguments:
            *types: The argument types for which some function should be run_func
        Returns:
            A function to be passed a Callable to register for the
            argument types passed to `magic`.
        """

        def _magic(func: MagicFunc) -> Magic:
            registration = MagicRegistration(types=types, function=func)
            self.funcref.append(registration)
            return self

        return _magic

    def should_expand(self, *args: TypeUnion) -> bool:
        return False

    @staticmethod
    def cartesian_product(args: Sequence[TypeUnion]) -> Iterator[Sequence[CExpr]]:
        return product(*(arg.expressions for arg in args))

    @staticmethod
    def unexpanded(args: Sequence[TypeUnion]) -> bool:
        return any(isinstance(arg, VariableTypeUnion) for arg in args)

    @staticmethod
    def expand(args: Sequence[TypeUnion]) -> Sequence[TypeUnion]:
        newargs = []
        for arg in args:
            if isinstance(arg, VariableTypeUnion):
                newargs.append(arg.expand())
            else:
                newargs.append(arg)
        return newargs

    def __call__(self, *args: TypeUnion) -> TypeUnion:
        """
        Call this Magic on the arguments. This will call the
        registered handler function (if it exists) for each element of
        the Cartesian product of expressions in the TypeUnions. The
        return values from the handlers which are called will be added
        to the resulting `TypeUnion`. n-tuples of the Cartesian
        product for which handlers do not exist will be skipped.
        """
        log.info(f"Called {self.__class__} on {args}")
        functions = []
        if self.should_expand(*args) and Magic.unexpanded(args):
            print("Expanding", args)
            newargs = Magic.expand(args)
            print("Expanded", newargs)
            return self(*newargs)
        for arg_tuple in Magic.cartesian_product(args):
            func = self.__select(tuple(arg.expr.sort() for arg in arg_tuple))
            if func is None:
                continue
            functions.append((func, cast(Tuple, arg_tuple)))
        exprs = []
        sorts = set()
        for func, args in functions:
            res = self.__call_on_exprs(func.function, args)
            if res is None:
                continue
            exprs.append(res)
            sorts.add(res.expr.sort())
        if len(exprs) == 0 and Magic.unexpanded(args):
            newargs = Magic.expand(args)
            return self(*newargs)
        return TypeUnion(exprs, sorts)

    def __call_on_exprs(
        self, func: Callable[..., Expression], args: Tuple
    ) -> Optional[CExpr]:
        log.info(f"Trying to run implementation for type-pair {args}")

        try:
            res = func(*(arg.expr for arg in args))
            if res is None:
                return None
        except Exception as e:
            raise RuntimeError(
                f"Problem running {func}({', '.join(str(a) for a in args)})"
            ) from e
        constraints = list(concat(arg.constraints for arg in args))
        return CExpr(expr=res, constraints=constraints)

    def __select(self, args: Tuple) -> Optional[MagicRegistration]:
        log.info(f"Selecting implementation using {args}")

        def fuzzy_sort_equality(sub: z3.SortRef, parent: z3.SortRef) -> bool:
            return parent == sub or parent.subsort(sub)

        def fuzziest(left: z3.SortRef, right: z3.SortRef) -> z3.SortRef:
            if fuzzy_sort_equality(left, right):
                return right
            else:
                return left

        def sort_compare(arg_sort: z3.SortRef, func_key: TagType) -> bool:
            if isinstance(func_key, z3.SortRef):
                return fuzzy_sort_equality(arg_sort, func_key)
            elif isinstance(func_key, type):
                return isinstance(arg_sort, func_key)

        for registration in self.funcref:
            log.info(f"Checking {registration.types} against {args}")
            if all(sort_compare(*tu) for tu in zip(args, registration.types)):
                return registration
        return None
