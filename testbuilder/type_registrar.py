from __future__ import annotations

from typing import Generator, List, Optional, Tuple, cast

import z3
from dataclasses import dataclass
from logbook import Logger
from typeassert import assertify
from z3 import DatatypeRef

from .constrained_expression import ConstrainedExpression as CExpr, ConstraintSet
from .expandable_type_union import ExpandableTypeUnion
from .store_array import StoreArray
from .type_union import TypeUnion
from .variable_type_union import VariableTypeUnion
from .z3_types import AnyT, Expression, NilSort, Reference, SortSet, bool_and, bool_or

log = Logger("type_registrar")


@dataclass
class TypeRegistrar:
    anytype: z3.DatatypeSortRef
    reftype: Optional[z3.DatatypeSortRef]

    def store(self, name: str) -> StoreArray:
        assert self.reftype is not None
        return cast(StoreArray, z3.Array(name, Reference, self.reftype))

    def ref_constructors(self) -> Generator[z3.FuncDeclRef, None, None]:
        if self.reftype is None:
            return
        for i in range(self.reftype.num_constructors()):
            yield self.reftype.constructor(i)

    @assertify
    def AllTypes(self, name: str, restricted: SortSet = set()) -> VariableTypeUnion:
        """
        Args:
            name: The variable name to create
            restricted: If non-empty, the name will be treated as
                already restricted to this set of sorts. If there is only
                one sort in the set, the name will be treated as always
                having that sort. If empty, the name will be
                unrestricted, as with expand.
        """
        if len(restricted) > 0:
            union = self.expand(name)
            sorts: SortSet = {
                e.expr.sort() for e in union.expressions if e.expr.sort() in restricted
            }

            log.debug(f"Restricting new VariableAnyType for {name} to sorts: {sorts}")
            expressions: List[CExpr] = []
        else:
            sorts = set()
            expressions = [CExpr(expr=self.make_any(name))]
        return VariableTypeUnion(
            expressions=expressions, sorts=sorts, name=name, registrar=self
        )

    def make_any(self, name: str) -> AnyT:
        return cast(AnyT, z3.Const(name, self.anytype))

    def expand(self, name: str, types: SortSet = set()) -> TypeUnion:
        """
        Arguments:
            name: The variable name to expand
            types: A set of sorts to restrict the variable to. If the
                set is empty, does not restrict the variable at all.
        """
        var = self.make_any(name)
        exprs, sorts = self.expand_anytype_val(name, var, types)
        return TypeUnion(exprs, sorts)

    def expand_reference(
        self, union: TypeUnion, types: SortSet = set(), name: Optional[str] = None
    ) -> TypeUnion:
        """
        This function is the equivalent of `expand` but for full
        TypeUnions. It expands the values in each

        Arguments:
            union: A type union to expand values in
            types: A set of sorts to restrict the results to. If the
                set is empty, does not restrict the results at all.
        """
        assert self.reftype is not None
        exprs = []
        sorts: SortSet = set()
        for orig_cexpr in union.expressions:
            val = orig_cexpr.expr
            # Support non-anytype values
            if val.sort() != self.anytype:
                exprs.append(orig_cexpr)
                sorts.add(orig_cexpr.expr.sort())
                continue
            if name is None:
                local_name = str(val)
            else:
                local_name = name
            expr_exprs, expr_sorts = self.expand_anytype_val(
                local_name, cast(AnyT, val), types, orig_cexpr.constraints
            )
            log.info(f"Expanded value {val} to {expr_exprs} {expr_sorts}")
            exprs += expr_exprs
            sorts |= expr_sorts
        return TypeUnion(exprs, sorts)

    def expand_anytype_val(
        self,
        name: str,
        val: AnyT,
        types: SortSet = set(),
        orig_constraints: ConstraintSet = set(),
    ) -> Tuple[List[CExpr], SortSet]:
        """
        Takes an Any value and extracts all possible results from it,
        limiting by types.

        Arguments:
            name: A string to use as the name value for the
                  constraints created during expansion
            orig_constraints: A list of constraints which might
                              already be placed on the value being
                              passed in. These will be added to each
                              of the new values' constraints list.
        """
        exprs = []
        sorts: SortSet = set()
        for i in range(self.anytype.num_constructors()):
            constructor = self.anytype.constructor(i)
            if constructor.arity() == 1:
                expr = self.anytype.accessor(i, 0)(val)
            else:
                expr = val
            # Allow restricting the expansion of the variable
            if len(types) > 0:
                if expr.sort() not in types:
                    log.debug(
                        f"Expansion restricted to {types}; discarding {constructor.name()}"
                    )
                    continue
            if len(types) == 1:
                cexpr = CExpr(expr=expr)
            else:
                constraint = self.anytype.recognizer(i)(val)
                constraints = orig_constraints | {(name, expr.sort(), constraint)}
                cexpr = CExpr(expr=expr, constraints=constraints)
            exprs.append(cexpr)
            sorts.add(expr.sort())
        log.debug(f"Returning exprs of {exprs}")
        return exprs, sorts

    def _extract_or_wrap(self, val: Expression, extractor: str, wrapper: str) -> AnyT:
        acc = getattr(self.anytype, extractor, None)
        if acc is not None and val.decl() == acc:
            return cast(AnyT, val.arg(0))
        wrap_func = getattr(self.anytype, wrapper)
        return cast(AnyT, wrap_func(val))

    def wrap(self, val: Expression) -> AnyT:
        """Take a raw Z3 value and wrap it in an Any.

        Args:
            val: The value to wrap
        Return:
            The same value in an Any
        """
        if val.sort() == z3.IntSort():
            return self._extract_or_wrap(val, "i", "Int")
        if val.sort() == z3.StringSort():
            return self._extract_or_wrap(val, "s", "String")
        if val.sort() == z3.BoolSort():
            return self._extract_or_wrap(val, "b", "Bool")
        if val.sort() == Reference:
            return self._extract_or_wrap(val, "r", "Reference")
        # if val.sort() == self.anytype:
        #     return self._extract_or_wrap(val, "n", "Nil")
        if val.sort() == self.anytype:
            # This can happen if we already have a wrapped type, or if
            # the type is a non-wrapper type
            return val  # type: ignore
        raise RuntimeError("Unknown type being wrapped")

    @assertify
    def assign(self, target: DatatypeRef, value: TypeUnion) -> TypeUnion:
        if isinstance(value, ExpandableTypeUnion):
            # Special-case for TypeUnions which are already Any variables
            return TypeUnion.wrap(target == value._get_any())
        exprs = []
        for expr in value.expressions:
            assign = target == self.wrap(expr.expr)
            if expr.constrained():
                exprs.append(bool_and([assign, expr.constraint()]))
            else:
                exprs.append(assign)

        return TypeUnion.wrap(bool_or(exprs))

    def expr_to_boolean(self, expr: Expression) -> z3.BoolRef:
        """
        Apply Python's truthy standards to make a boolean of an
        expression.
        """
        if z3.is_int(expr):
            return expr != z3.IntVal(0)
        elif z3.is_bool(expr):
            return cast(z3.BoolRef, expr)
        elif z3.is_string(expr):
            return z3.Length(cast(z3.String, expr)) != z3.IntVal(0)
        elif expr.sort() == self.anytype:
            nil = getattr(self.anytype, "Nil", None)
            if expr.decl() == nil.decl():
                return z3.BoolVal(False)
            else:
                # For all anytype values that aren't None, assume they
                # are true. This will not be the case for some types,
                # but it's true for our current set of types
                return z3.BoolVal(True)
        elif expr.sort() == self.reftype:
            is_pair = getattr(self.reftype, "is_Pair", None)
            if is_pair is None:
                raise RuntimeError("No is_Pair available for reftype")
            return z3.BoolVal(True)
        raise UnknownConversionException(
            f"Can't convert {expr.sort().name()} ({expr.decl().name()}) to boolean"
        )

    def unwrap(self, val: Expression) -> Expression:
        """
        Extracts a value from an Any type.

        Assumes all constructors for Any take a single argument, which is the
        value stored in them.
        """
        if val.sort() == self.anytype:
            if val.num_args() == 1:
                return val.arg(0)
        return val


class UnknownConversionException(RuntimeError):
    pass
