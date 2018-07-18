import ast
import z3  # type: ignore
from typing import Any
from inspect import getmembers
import re

EVAL_GLOBALS = {"z3": z3, "true": z3.BoolVal(True), "false": z3.BoolVal(False)}
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
        zzz = ast.Name("z3", ast.Load())
        typekey, varname = split_varname(node.id)
        print('name', typekey, varname)

        if typekey:
            if typekey == 's':
                sort_name = "String"
            elif typekey == 'b':
                sort_name = "Bool"
            else:
                sort_name = "Int"
        else:
            sort_name = "Int"
        sort_call = ast.Attribute(zzz, sort_name, ast.Load())
        call = ast.Call(sort_call, [ast.Str(varname)], [])
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


def expand_variables(code: str) -> Any:
    code_tree = ast.parse(code.strip(), mode="eval")
    visitor = VariableExpansionVisitor()
    expanded_code = visitor.visit(code_tree)
    # print(ast.dump(expanded_code, include_attributes=True))
    print("Processed these variables as literals:", visitor.literals)
    return eval(
        compile(expanded_code, filename="<string>", mode="eval"),
        EVAL_GLOBALS,
        EVAL_LOCALS,
    )
