import ast
import re
from inspect import getmembers
from typing import Any

from astor import to_source  # type: ignore

import z3  # type: ignore

from .z3_types import Any as AnyType, TypeRegistrar

Registrar = TypeRegistrar(AnyType)

EVAL_GLOBALS = {
    "z3": z3,
    "true": z3.BoolVal(True),
    "false": z3.BoolVal(False),
    "type": type,
    "Any": Registrar.anytype,
    "make_any": Registrar.make_any,
}
MAGIC_FUNCS = {"z3": {"Int", "String"}, "make_any": None}
EVAL_LOCALS = dict(getmembers(z3))
# It seems `d` is defined as NoneType, and we would really like it to be
# available for general use. Delete all variables from z3 of length 1:
def clean_locals():
    deletes = []
    for var in EVAL_LOCALS.keys():
        if len(var) == 1:
            deletes.append(var)
    print("Deleting these attributes from z3:", deletes)
    for var in deletes:
        del EVAL_LOCALS[var]


clean_locals()

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
    def __init__(self):
        super().__init__()
        self.literals = []

    def visit_Name(self, node: ast.Name) -> ast.AST:
        if node.id in EVAL_GLOBALS or node.id in EVAL_LOCALS:
            # We don't want to treat variables in globals or locals as auto
            # variables
            self.literals.append(node.id)
            return node
        # zzz = ast.Name("z3", ast.Load())
        typekey, varname = split_varname(node.id)
        # # print('name', typekey, varname)

        # if typekey:
        #     if typekey == "s":
        #         sort_name = "String"
        #     elif typekey == "b":
        #         sort_name = "Bool"
        #     else:
        #         sort_name = "Int"
        # else:
        #     sort_name = "Int"
        # sort_call = ast.Attribute(zzz, sort_name, ast.Load())
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
            if func.id in MAGIC_FUNCS:
                self.literals.append(func.id)
                return node
        return self.generic_visit(node)

    def visit_Attribute(self, node: ast.Attribute) -> ast.Attribute:
        # value = self.visit(node.value)
        value = node.value
        # print("attrib", ast.dump(node))
        if isinstance(value, ast.Name):
            # print("magic thing", value.id)
            if value.id in MAGIC_FUNCS:
                funcs = MAGIC_FUNCS[value.id]
                if funcs is None:
                    self.literals.append(value.id)
                    return node
                else:
                    if node.attr in funcs:
                        self.literals.append(f"{value.id}.{node.attr}")
                        return node
        return self.generic_visit(node)
        # attribute = ast.Attribute(value, node.attr, node.ctx)
        # return ast.fix_missing_locations(ast.copy_location(attribute, node))

    def visit_BinOp(self, node: ast.BinOp) -> ast.AST:
        op_type = type(node.op)
        if op_type in MagicOps:
            left = self.visit(node.left)
            right = self.visit(node.right)
            op = MagicOps[op_type]
            zzz = ast.Name("z3", ast.Load())
            op_attr = ast.Attribute(zzz, op, ast.Load())
            call = ast.Call(op_attr, [left, right], [])
            return ast.fix_missing_locations(ast.copy_location(call, node))
        else:
            return self.generic_visit(node)

    def visit_BoolOp(self, node: ast.BinOp) -> ast.AST:
        op_type = type(node.op)
        if op_type in MagicOps:
            values = [self.visit(v) for v in node.values]
            op = MagicOps[op_type]
            zzz = ast.Name("z3", ast.Load())
            op_attr = ast.Attribute(zzz, op, ast.Load())
            call = ast.Call(op_attr, values, [])
            return ast.fix_missing_locations(ast.copy_location(call, node))
        else:
            return self.generic_visit(node)

    def visit_UnaryOp(self, node: ast.UnaryOp) -> ast.AST:
        op_type = type(node.op)
        if op_type in MagicOps:
            operand = self.visit(node.operand)
            op = MagicOps[op_type]
            zzz = ast.Name("z3", ast.Load())
            op_attr = ast.Attribute(zzz, op, ast.Load())
            call = ast.Call(op_attr, [operand], [])
            return ast.fix_missing_locations(ast.copy_location(call, node))
        else:
            return self.generic_visit(node)


class ExpansionTester(ast.NodeVisitor):
    def generic_visit(self, node: ast.AST) -> bool:
        super().generic_visit(node)
        if isinstance(node, ast.stmt) or isinstance(node, ast.expr):
            if not isinstance(node, ast.Expression):
                node = ast.copy_location(ast.Expression(node), node)
            expr = compile(node, filename="<ExpansionTester>", mode="eval")
        else:
            return True
        try:
            eval(expr, EVAL_GLOBALS, EVAL_LOCALS)
        except z3.z3types.Z3Exception as e:
            raise RuntimeError(
                f"Expansion test failed while expanding\n{to_source(node)}\nError: {e}"
            ) from e
        except TypeError as e:
            raise RuntimeError(
                f"Expansion test failed while expanding\n{to_source(node)}\nError: {e}"
            ) from e
        return True


def expand_variables(code: str) -> Any:
    code_tree = ast.parse(code.strip(), mode="eval")
    visitor = VariableExpansionVisitor()
    expanded_code = visitor.visit(code_tree)
    # print("expanded AST", ast.dump(expanded_code, include_attributes=True))
    print("Processed these variables as literals:", visitor.literals)
    ExpansionTester().visit(expanded_code)
    return eval(
        compile(expanded_code, filename="<string>", mode="eval"),
        EVAL_GLOBALS,
        EVAL_LOCALS,
    )
