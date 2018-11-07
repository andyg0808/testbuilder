import ast
import re
from inspect import getmembers
from typing import Any, Mapping, NoReturn, Optional

from astor import to_source  # type: ignore

import z3  # type: ignore

from .type_registrar import TypeRegistrar

# Functions whose arguments should be left untouched (i.e., they
# should be left as the standard Python types)
MAGIC_FUNCS = {"z3": {"Int", "String", "Array", "Store"}, "make_any": None}

# Operators which should be redefined to do z3 operations
MagicOps = {
    ast.BitOr: "Or",
    ast.BitAnd: "And",
    ast.Invert: "Not",
    ast.And: "And",
    ast.Or: "Or",
    ast.Not: "Not",
}

NAME_PARSER = re.compile(r"(.)?(pyname_.*)")


def split_varname(name):
    match = NAME_PARSER.fullmatch(name)
    if match:
        return match[1], match[2]
    else:
        return False, name


class VariableExpansionVisitor(ast.NodeTransformer):
    def __init__(self, eval_globals, eval_locals, magic_funcs, magic_ops):
        super().__init__()
        self.literals = []
        self.eval_globals = eval_globals
        self.eval_locals = eval_locals
        self.magic_funcs = magic_funcs
        self.magic_ops = magic_ops

    def visit_Name(self, node: ast.Name) -> ast.AST:
        if node.id in self.eval_globals or node.id in self.eval_locals:
            # We don't want to treat variables in globals or locals as auto
            # variables
            self.literals.append(node.id)
            return node
        typekey, varname = split_varname(node.id)
        any_func = ast.Name("make_any", ast.Load())
        call = ast.Call(any_func, [ast.Str(varname)], [])
        return ast.fix_missing_locations(ast.copy_location(call, node))

    def visit_Str(self, node: ast.Str) -> ast.AST:
        zzz = ast.Name("z3", ast.Load())
        str_sort = ast.Attribute(zzz, "StringVal", ast.Load())
        call = ast.Call(str_sort, [node], [])
        return ast.fix_missing_locations(ast.copy_location(call, node))

    def visit_Num(self, node: ast.Num) -> ast.AST:
        zzz = ast.Name("z3", ast.Load())
        if int(node.n) == node.n:
            num_sort = ast.Attribute(zzz, "IntVal", ast.Load())
        else:
            raise RuntimeError("Non-integer constants unsupported")
        call = ast.Call(num_sort, [node], [])
        return ast.fix_missing_locations(ast.copy_location(call, node))

    def visit_Call(self, node: ast.Call) -> ast.Call:
        func = node.func
        if isinstance(func, ast.Name):
            if func.id in self.magic_funcs:
                self.literals.append(func.id)
                return node
        elif isinstance(func, ast.Attribute):
            if self.is_magic(func):
                self.literals.append(self.magic_name(func))
                return node
        return self.generic_visit(node)

    def magic_name(self, node: ast.Attribute) -> str:
        value = node.value
        assert isinstance(value, ast.Name)
        funcs = self.magic_funcs[value.id]
        if funcs is None:
            return value.id
        else:
            return f"{value.id}.{node.attr}"

    def is_magic(self, node: ast.Attribute) -> bool:
        value = node.value
        if isinstance(value, ast.Name):
            if value.id in self.magic_funcs:
                funcs = self.magic_funcs[value.id]
                if funcs is None:
                    return True
                else:
                    if node.attr in funcs:
                        return True
        return False

    def visit_BinOp(self, node: ast.BinOp) -> ast.AST:
        op_type = type(node.op)
        if op_type in self.magic_ops:
            left = self.visit(node.left)
            right = self.visit(node.right)
            op = self.magic_ops[op_type]
            zzz = ast.Name("z3", ast.Load())
            op_attr = ast.Attribute(zzz, op, ast.Load())
            call = ast.Call(op_attr, [left, right], [])
            return ast.fix_missing_locations(ast.copy_location(call, node))
        else:
            return self.generic_visit(node)

    def visit_BoolOp(self, node: ast.BinOp) -> ast.AST:
        op_type = type(node.op)
        if op_type in self.magic_ops:
            values = [self.visit(v) for v in node.values]
            op = self.magic_ops[op_type]
            zzz = ast.Name("z3", ast.Load())
            op_attr = ast.Attribute(zzz, op, ast.Load())
            call = ast.Call(op_attr, values, [])
            return ast.fix_missing_locations(ast.copy_location(call, node))
        else:
            return self.generic_visit(node)

    def visit_UnaryOp(self, node: ast.UnaryOp) -> ast.AST:
        op_type = type(node.op)
        if op_type in self.magic_ops:
            operand = self.visit(node.operand)
            op = self.magic_ops[op_type]
            zzz = ast.Name("z3", ast.Load())
            op_attr = ast.Attribute(zzz, op, ast.Load())
            call = ast.Call(op_attr, [operand], [])
            return ast.fix_missing_locations(ast.copy_location(call, node))
        else:
            return self.generic_visit(node)


class ExpansionTester(ast.NodeVisitor):
    def __init__(self, eval_globals, eval_locals):
        self.eval_globals = eval_globals
        self.eval_locals = eval_locals

    def generic_visit(self, node: ast.AST) -> bool:
        super().generic_visit(node)
        if isinstance(node, ast.stmt) or isinstance(node, ast.expr):
            if not isinstance(node, ast.Expression):
                node = ast.copy_location(ast.Expression(node), node)
            expr = compile(node, filename="<ExpansionTester>", mode="eval")
        else:
            return True

        def fail(reason: Exception) -> NoReturn:
            raise RuntimeError(
                f"Expansion test failed while expanding\n{to_source(node)}\nError: {e}"
            ) from e

        try:
            eval(expr, self.eval_globals, self.eval_locals)
        except z3.z3types.Z3Exception as e:
            fail(e)
        except TypeError as e:
            fail(e)
        except z3.ArgumentError as e:
            fail(e)
        return True


def expand_variables(
    code: str, registrar: TypeRegistrar, local_vals: Optional[Mapping[str, Any]] = None
) -> Any:
    # Values to include as globals during evaluation
    eval_globals = {
        "z3": z3,
        "true": z3.BoolVal(True),
        "false": z3.BoolVal(False),
        "type": type,
        "Any": registrar.anytype,
        "make_any": registrar.make_any,
    }

    # Values to include as locals during evaluation
    eval_locals = dict(getmembers(z3))
    if local_vals is not None:
        eval_locals.update(local_vals)
    # It seems `d` is defined as NoneType, and we would really like it to be
    # available for general use. Delete all variables from z3 of length 1:
    def clean_locals():
        deletes = []
        for var in eval_locals.keys():
            if len(var) == 1:
                deletes.append(var)
        print("Deleting these attributes from z3:", deletes)
        for var in deletes:
            del eval_locals[var]

    clean_locals()
    code_tree = ast.parse(code.strip(), mode="eval")
    visitor = VariableExpansionVisitor(eval_globals, eval_locals, MAGIC_FUNCS, MagicOps)
    expanded_code = visitor.visit(code_tree)
    # print("expanded AST", ast.dump(expanded_code, include_attributes=True))
    print("Processed these variables as literals:", visitor.literals)
    ExpansionTester(eval_globals, eval_locals).visit(expanded_code)
    return eval(
        compile(expanded_code, filename="<string>", mode="eval"),
        eval_globals,
        eval_locals,
    )
