from __future__ import annotations

import inspect
import traceback
from itertools import product
from typing import (
    Any,
    Callable,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
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
from .expandable_type_union import ExpandableTypeUnion
from .type_union import TypeUnion
from .z3_types import Expression, SortMarker, SortSet

log = Logger("Magic")


T = TypeVar("T")

MagicFunc = Callable[..., T]
TagType = Union[z3.SortRef, Type[Any]]
ConstraintFunc = Callable[..., Set[z3.BoolRef]]


@dataclass(frozen=True)
class MagicTag:
    types: Sequence[TagType]
    constraint_func: Optional[ConstraintFunc]


def magic_tag(
    *types: TagType, constraint: Optional[ConstraintFunc] = None
) -> Callable[[MagicFunc[T]], MagicFunc[T]]:
    def _magic(func: MagicFunc[T]) -> MagicFunc[T]:
        setattr(func, "__magic", MagicTag(types=types, constraint_func=constraint))
        return func

    return _magic


@dataclass(frozen=True)
class MagicRegistration(MagicTag):
    function: MagicFunc[Any]


SortingFunc = Callable[[Expression], Optional[SortMarker]]


class MagicFountain:
    def __init__(self, sorting: SortingFunc) -> None:
        self.sorting = sorting

    def __call__(
        self, *types: TagType, constraint: Optional[ConstraintFunc] = None
    ) -> Callable[[MagicFunc[T]], Magic]:
        return Magic.m(self.sorting, types, constraint=constraint)


class Magic:
    """
    Function overloading and abstract type handling.

    A `Magic` is a callable object which accepts any number of
    `TypeUnion` s as arguments. It searches for registered handler
    functions for each element of the Cartesian product of all the
    expressions in each `TypeUnion`. It discards those n-tuples of
    types which do not have defined handlers. For those which do have
    handlers, it calls the handler with the expressions from the
    n-tuple.

    """

    def __init__(self, sorting: SortingFunc) -> None:
        self.sorting = sorting
        stack = traceback.extract_stack()
        filtered_stack = [s for s in stack if s.filename != __file__]
        self.definition = filtered_stack[-1]
        if not hasattr(self, "name"):
            self.name = (
                f"{self.__class__} (created at "
                f"{self.definition.filename}:{self.definition.lineno} "
                f"in {self.definition.name})"
            )
        self.funcref: List[MagicRegistration] = []
        for _, method in inspect.getmembers(self, inspect.ismethod):
            magic = getattr(method, "__magic", None)
            if magic is not None:
                registration = MagicRegistration(
                    function=method,
                    types=magic.types,
                    constraint_func=magic.constraint_func,
                )
                self.funcref.append(registration)

    @staticmethod
    def m(
        sorting: Optional[SortingFunc],
        types: Sequence[TagType],
        constraint: Optional[ConstraintFunc],
    ) -> Callable[[MagicFunc[Any]], Magic]:
        """
        Create an instance of Magic and call `magic` on it with these
        arguments.
        """
        if not sorting:
            res = Magic(lambda x: x.sort())
        else:
            res = Magic(sorting)
        return res.magic(types, constraint)

    def magic(
        self, types: Sequence[TagType], constraint: Optional[ConstraintFunc]
    ) -> Callable[[MagicFunc[Any]], Magic]:
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

        def _magic(func: MagicFunc[Any]) -> Magic:
            registration = MagicRegistration(
                types=types, function=func, constraint_func=constraint
            )
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
        return any(isinstance(arg, ExpandableTypeUnion) for arg in args)

    @staticmethod
    def expand(args: Sequence[TypeUnion]) -> Sequence[TypeUnion]:
        newargs = []
        for arg in args:
            if isinstance(arg, ExpandableTypeUnion):
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
        log.info(f"Called {self.name}\non {args}")
        functions = []
        if self.should_expand(*args) and Magic.unexpanded(args):
            log.debug("Expanding {}", args)
            newargs = Magic.expand(args)
            log.debug("Expanded {}", newargs)
            return self(*newargs)
        for arg_tuple in Magic.cartesian_product(args):
            func = self.__select(tuple(arg.expr.sort() for arg in arg_tuple))
            if func is None:
                continue
            functions.append((func, cast(Tuple[Any], arg_tuple)))
        exprs = []
        sorts: SortSet = set()
        found_none = False
        for func, arg_tuple in functions:
            res = self.__call_on_exprs(func, arg_tuple)
            if res is None:
                continue
            exprs.append(res)
            sort = self.sorting(res.expr)
            if sort is not None:
                sorts.add(sort)
            else:
                found_none = True
        if found_none:
            # The sorts list should be empty if we found a None value
            # because an empty sort list is treated as an Any, and the
            # None value means any sort is allowed.  This is only an
            # issue because we're caching the set of sorts that the
            # `CExpr`s in our `TypeUnion` have. If we looked at each
            # one each time, we could check if its type is applicable,
            # and we could directly check if an AnyType is allowed.
            assert len(sorts) == 0
        if len(exprs) == 0 and Magic.unexpanded(args):
            log.info(f"No results for {args} Expanding and retrying.")
            newargs = Magic.expand(args)
            return self(*newargs)
        elif len(exprs) == 0:
            log.info(
                f"No results for {args}. Could not expand. Returning empty TypeUnion"
            )
        else:
            arg_lines = ",\n".join(str(x) for x in args)
            arg_lines = f"({arg_lines})"
            log.info(f"Results below for args\n{arg_lines}")
            log.info(f"Results\n{exprs}")
        return TypeUnion(exprs, sorts)

    def __call_on_exprs(
        self, reg: MagicRegistration, args: Tuple[Any]
    ) -> Optional[CExpr]:
        log.info(f"Trying to run implementation for type-pair {args}")

        arg_exprs = [arg.expr for arg in args]
        try:
            res = reg.function(*arg_exprs)
            if res is None:
                return None
        except Exception as e:
            raise RuntimeError(
                f"Problem running {reg.function}({', '.join(str(a) for a in args)})"
            ) from e
        constraints = set(concat(arg.constraints for arg in args))
        if reg.constraint_func:
            new_constraint = reg.constraint_func(*arg_exprs)
            constraints |= {(str(i), None, i) for i in new_constraint}
        return CExpr(expr=res, constraints=constraints)

    def __select(self, args: Sequence[z3.SortRef]) -> Optional[MagicRegistration]:
        log.info(f"Selecting implementation using {args}")

        def sort_compare(arg_sort: z3.SortRef, func_key: TagType) -> bool:
            if isinstance(func_key, z3.SortRef):
                return arg_sort == func_key
            elif isinstance(func_key, type):
                return isinstance(arg_sort, func_key)
            raise RuntimeError(
                f"Unexpected type for func_key: {type(func_key)} is not a TagType"
            )

        for registration in self.funcref:
            log.info(f"Checking if {registration.types} implements for {args}")
            if all(sort_compare(*tu) for tu in zip(args, registration.types)):
                log.info(f"Yes, {registration} implements for {args}")
                return registration
        return None
