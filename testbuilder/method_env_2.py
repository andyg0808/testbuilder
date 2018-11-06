import ast

# import IPython
from termcolor import cprint


class AnnotationResult:
    def __init__(self, result, ops):
        self.ops = ops
        self.result = result


class SymbolicExpressionConverter(ast.NodeVisitor):
    def method(self, name, attr, args):
        return ast.Call(self.attribute(name, attr), args, [])

    def attribute(self, name, attr):
        return ast.Attribute(ast.Name(name, ast.Load()), attr, ast.Load())

    def lookup(self, name, attr, args):
        if args:
            return self.method(name, attr, args)
        else:
            return self.attribute(name, attr)

    def z3(self, name, args=None):
        return self.lookup("z3", name, args)

    def symb(self, name, args=None):
        return self.lookup("__symb", name, args)

    def boolean(self, value):
        conds = []

        return conds

    def visit_Num(self, node):
        return self.z3("IntVal", [node])

    def visit_Name(self, node):
        return ast.copy_location(ast.Name("symb_" + node.id, node.ctx), node)

    # def visit_BinOp(self, node):
    #     return ast.copy_location(ast.BinOp(self.visit(node.left),
    #                                        node.op,
    #                                        self.visit(node.right)),
    #                              node)

    def visit_NameConstant(self, node):
        if isinstance(node.value, bool):
            return self.z3("BoolVal", [node])
        IPython.embed()

    def generic_visit(self, node):
        cprint(node, "blue")
        vis = super().generic_visit(node)
        if vis:
            return vis
        else:
            return node


class AnnotateModule(ast.NodeTransformer):
    def __init__(self):
        self.conv = SymbolicExpressionConverter()
        self.names = []

    def visit_Module(self, node):
        self.generic_visit(node)
        lines = []
        lines.append(ast.Import([ast.alias("z3", None)]))
        lines.append(ast.Import([ast.alias("symb_util", None)]))
        lines.append(
            ast.Assign(
                [ast.Name("__symb", ast.Store())],
                self.conv.method("symb_util", "Symbolics", []),
            )
        )
        node.body[0:0] = lines
        return node

    def visit_Assign(self, node):
        self.generic_visit(node)

        def gather_names(name):
            if isinstance(name, ast.Name):
                return name.id

        self.names += map(gather_names, ast.walk(node.targets))
        cprint(self.names, "yellow")
        return node

    def visit_Name(self, node):
        if node.id in self.names:
            node.id = "conc_" + node.id
        return node

    def visit_arg(self, node):
        node.arg = "conc_" + node.arg
        return node

    def _args_to_symb(self, args):
        lines = []
        for arg in args.args:
            id = arg.arg
            lines.append(
                ast.Assign(
                    [ast.Name("symb_" + id, ast.Store())],
                    self.conv.z3("Const", [ast.Str(id), self.conv.symb("obj_sort")]),
                )
            )
            self.names.append(id)
        return lines

    def visit_FunctionDef(self, node):
        self.names = []
        symb_args = self._args_to_symb(node.args)
        i = ast.Assign([ast.Name("__path", ast.Store())], ast.List([], ast.Load()))
        self.generic_visit(node)
        node.body[0:0] = symb_args
        node.body.insert(0, i)
        return node

    def visit_Call(self, node):
        return ast.Subscript(
            self.generic_visit(node), ast.Index(ast.Num(0)), ast.Load()
        )

    def visit_Return(self, node):
        symb_value = self.conv.visit(node.value)
        self.generic_visit(node)
        lst = ast.List(
            [node.value, symb_value, ast.Name("__path", ast.Load())], ast.Load()
        )
        ret = ast.Return(lst)
        return ret

    def visit_If(self, node):
        symb_cond = self.conv.visit(node.test)
        self.generic_visit(node)
        true_cond = self.conv.method("__path", "append", [symb_cond])
        false_cond = self.conv.method(
            "__path", "append", [self.conv.z3("Not", [symb_cond])]
        )
        node.body.insert(0, ast.Expr(true_cond))
        node.orelse.insert(0, ast.Expr(false_cond))
        return node

    # def visit_FunctionDef(self, node):
    #     annotated =
    #     return node['

    # def visit_Module(self, node):
    #     code = []
    #     for i in node.body:
    #         print(i)
    #         code += self.visit(i)
    #     return ast.Module(code)

    # def generic_visit(self, node):
    #     return [node]
