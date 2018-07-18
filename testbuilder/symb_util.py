import functools

import z3


class Symbolics:

    def __init__(self):
        self.any_sort = z3.DeclareSort("Any")
        self.obj_sort = z3.DeclareSort("Obj")
        self.py_int = z3.Const("Int", self.obj_sort)
        self.none = z3.Const("None", self.obj_sort)
        self.to_int = z3.Function("toInt", self.obj_sort, z3.IntSort())

    def symb_from_python(self, name, value):
        if isinstance(value, bool):
            return z3.Bool(name)
        if isinstance(value, int):
            return z3.Int(name)
        if isinstance(value, float):
            return z3.Real(name)
        return z3.Const(str(name), self.obj_sort)

    def z3_to_python(self, value):
        if isinstance(value.sort(), z3.ArithSortRef):
            return value.as_long()
        if isinstance(value.sort(), z3.BoolSortRef):
            return z3.is_true(value)
        else:
            IPython.embed()
            return value.as_string()

    def z3_to_bool(self, value):
        conds = []
        conds.append(z3.And(value == self.py_int, self.to_int(value) != 0))
        return functools.reduce(lambda x, y: z3.And(x, y), conds)
