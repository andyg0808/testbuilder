import ast
from functools import partial
from pathlib import Path

from toolz import pipe

import z3

from .expression_builder import get_expression
from .type_builder import TypeBuilder
from .utils import colorize
from .variable_expander import expand_variables
from .z3_types import Reference, diff_expression, print_diff


class ExpressionChecker:
    def __init__(self, configure=None):
        builder = TypeBuilder()
        if configure is None:
            self.registrar = builder.construct()
        else:
            builder = configure(builder)
            self.registrar = builder.build()

    def __call__(
        self,
        code_string,
        expected,
        line=-1,
        simplify=False,
        write_tree="",
        depth: int = 1,
        overall=False,
    ):
        """
        Args:
            code_string: A string of code to create an expression for
            expected: The expected expression resulting from the string of code
            line: The line number on which to slice.
            simplify: Whether to run z3.simplify on the example and actual output
                      before comparing.
            write_tree: If nonempty, a filename to which to write the basic block
                        tree generated while converting the expression.
            depth: The loop unrolling depth to use
            overall: Whether to generate an expression which does not use a
                     particular slice of the code.

            The overall option forces the expression to include all exit points
            from the function. It still uses the line number to choose which code
            to include, but control structures will be included for all exit
            points. Currently does nothing.
        """

        if isinstance(expected, str):
            if self.registrar.reftype is None:
                expected = expand_variables(expected, self.registrar)
            else:
                store_sort = z3.ArraySort(Reference, self.registrar.reftype)
                local_vals = {
                    "store": z3.Const("store", store_sort),
                    "store_1": z3.Const("store_1", store_sort),
                    "store_2": z3.Const("store_2", store_sort),
                    "Reference": lambda i: Reference.Reference(i),
                }
                expected = expand_variables(
                    expected, self.registrar, local_vals=local_vals
                )
        _get_expression = partial(
            get_expression, self.registrar, Path("<path>"), line, depth=depth
        )
        test_data = pipe(code_string.strip(), ast.parse, _get_expression)
        if test_data is None:
            expr = None
        else:
            expr = test_data.expression
        print("expected  ", colorize(repr(expected)))
        print("expression", colorize(repr(expr)))
        if simplify:
            expected = z3.simplify(expected)
            expr = z3.simplify(expr)
        if expected is None:
            assert expr is None
        else:
            diff = diff_expression(expected, expr)
            if diff is not None:
                print_diff(diff)
                raise AssertionError("Expressions differ")
