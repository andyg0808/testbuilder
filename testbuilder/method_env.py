import z3
import random
import ast
from .result import Result
# import IPython
import itertools


class MethodEnv(ast.NodeVisitor):
    """
    Runs code concretely and symbolically.

    Treats the code as if it is all contained in a ``def``; to create a new
    environment, create a new instance of the class.
    """

    def __init__(self, arguments, arg_values=None):
        """Create a new environment for code execution."""
        self.any_sort = z3.DeclareSort('Any')
        self.obj_sort = z3.DeclareSort('Obj')
        self.none = z3.Const('None', self.obj_sort)
        arg_names = map(lambda arg: arg.arg, arguments.args)
        self.env = {}
        for i, name in enumerate(arg_names):
            sym_value = None
            if arg_values and name in arg_values:
                value = arg_values[name]
            elif arg_values and i < len(arg_values):
                value = arg_values[i]
            else:
                # Take type into account here
                value = random.random()
                sym_value = z3.Int(name)
            if sym_value is None:
                sym_value = self.symb_from_python(name, value)
            self.env[name] = Result(value, sym_value)
        self.constraint = []
        self._load_env()

    def _load_env(self):
        def _print(*args):
            conc, symb, seq = MethodEnv._split_args(args)
            return Result(print(conc), self.none, MethodEnv._flatten(seq))
        self.env['print'] = _print

    def _flatten(l):
        return itertools.chain(*l)

    def _split_args(args):
        splits = []
        for arg in args:
            for i,v in enumerate(arg):
                if i in splits:
                    splits[i].append(v)
                else:
                    splits.append([v])
        return splits

    def block(self, block):
        """Execute a block of code, returning the result of the last line."""
        ret = None
        for node in block:
            ret = self.stmt(node)
            # We only return non-None if the result should be returned
            if ret:
                return ret

    def pybool(self, expr):
        """
        Convert a z3 expression of arbitrary type into a Boolean.

        Follows Python boolean rules.
        """
        if isinstance(expr, z3.ArithRef):
            return expr == z3.IntVal(0)
        if isinstance(expr, z3.BoolRef):
            return expr
        if expr.sort() == self.obj_sort:
            return expr == self.none
        return z3.BoolVal(True)

    def stmt(self, node):
        return self.visit(node)

    def expr(self, node):
        return self.visit(node)

    def _crash(self, desc, node):
        dirlist = dir(node)
        dirlist.sort()
        print("Problem:")
        print(type(node))
        print(dirlist)
        raise Exception(desc)

    def visit_Return(self, node):
        if node.value:
            return self.visit(node.value)

    def visit_Expr(self, node):
        self.visit(node.value)
        return None
    def visit_If(self, node):
        cond = self.visit(node.test)
        bool_symb = self.pybool(cond.symbolic)
        if cond.concrete:
            ret = self.block(node.body)
            self.constraint.append(bool_symb)
        else:
            ret = self.block(node.orelse)
            self.constraint.append(z3.Not(bool_symb))
        return ret

    def visit_Add(self, node):
        return lambda a, b: a + b

    def visit_Sub(self, node):
        return lambda a, b: a - b

    def visit_Mult(self, node):
        return lambda a, b: a * b

    def visit_Div(self, node):
        return lambda a, b: a / b

    def visit_BinOp(self, node):
        left = self.expr(node.left)
        right = self.expr(node.right)
        op = self.visit(node.op)
        return op(left, right)

    def generic_visit(self, node):
        self._crash("Unknown node: {}".format(type(node)), node)

    def visit_Num(self, node):
        if isinstance(node.n, int):
            return Result(node.n, z3.IntVal(node.n))

    def visit_Str(self, node):
        return Result(node.s, z3.Const(node.s, self.obj_sort))

    def visit_NameConstant(self, node):
        if isinstance(node.value, str):
            if node.value in self.env:
                return self.env[node.value]
        if isinstance(node.value, bool):
            return Result(node.value, z3.BoolVal(node.value))
        if node.value is None:
            return Result(node.value, self.none)
        self._crash("Unknown constant: {}".format(node.value), node)

    def visit_Lt(self, node):
        return lambda a, b: a < b

    def visit_LtE(self, node):
        return lambda a, b: a <= b

    def visit_Gt(self, node):
        return lambda a, b: a > b

    def visit_GtE(self, node):
        return lambda a, b: a >= b

    def visit_Eq(self, node):
        return lambda a, b: a == b

    def visit_Not(self, node):
        return lambda a: a.invert(self.pybool)

    def visit_Compare(self, node):
        left = self.visit(node.left)
        comparators = map(self.visit, node.comparators)
        ops = map(self.visit, node.ops)
        result = Result.TRUE()
        for i in zip(ops, comparators):
            result = result.both_and(self.pybool, i[0](left, i[1]))
            left = i[1]
        return result

    def visit_UnaryOp(self, node):
        operand = self.visit(node.operand)
        op = self.visit(node.op)
        return op(operand)

    def visit_Name(self, node):
        if node.id in self.env:
            return self.env[node.id]
        else:
            self._crash("Unknown identifier", node)

    def visit_Assign(self, node):
        conc_values, sym_values, seq = self.visit(node.value)
        if not isinstance(conc_values, list):
            conc_values = [conc_values]
            sym_values = [sym_values]
            seq = [seq]
        vars = map(lambda t: t.id, node.targets)
        pairs = zip(vars, conc_values, sym_values, seq)
        for p in pairs:
            self.env[p[0]] = Result(p[1], p[2], p[3])

    def visit_IsExp(self, node):
        cond = self.expr(node.test)
        bool_symb = self.pybool(cond.symbolic)
        if cond.concrete:
            return self.visit(node.body).add_seq_elem(bool_symb)
        else:
            return self.visit(node.orelse).add_seq_elem(bool_symb)

    def visit_Call(self, node):
        func = self.visit(node.func)
        if func:
            args = map(self.visit, node.args)
            return func(*args)
        else:
            _crash("Unknown function", node)
