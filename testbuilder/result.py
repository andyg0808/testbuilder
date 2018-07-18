import z3
class Result:
    TRUE = lambda: Result(True, z3.BoolVal(True))

    def __init__(self, concrete, symbolic, sequence=None):
        self.concrete = concrete
        self.symbolic = symbolic
        if sequence:
            self.sequence = sequence
        else:
            self.sequence = ()

    def __add__(self, other):
        """Add (``+``) another Result to this one."""
        return Result(self.concrete + other.concrete, self.symbolic + other.symbolic)

    def __sub__(self, other):
        """Subtract (``-``) another Result from this one."""
        return Result(self.concrete - other.concrete, self.symbolic - other.symbolic)

    def __mul__(self, other):
        """Multiply (``*``) another Result by this one."""
        return Result(self.concrete * other.concrete, self.symbolic * other.symbolic)

    def op(self, oper, other):
        return Result(oper(self.concrete, other.concrete),
                      oper(self.symbolic, other.symbolic))

    def __lt__(self, other):
        return self.op(lambda a,b: a < b, other)

    def __le__(self, other):
        return self.op(lambda a,b: a <= b, other)

    def __gt__(self, other):
        return self.op(lambda a,b: a > b, other)

    def __ge__(self, other):
        return self.op(lambda a,b: a >= b, other)

    def __eq__(self, other):
        return self.op(lambda a,b: a == b, other)

    def invert(self, pybool):
        return Result(not self.concrete, z3.Not(pybool(self.symbolic)))

    def both_and(self, pybool, other):
        symb_bool = pybool(self.symbolic)
        other_symb_bool = pybool(other.symbolic)
        return Result(self.concrete and other.concrete, z3.And(symb_bool, other_symb_bool), self.sequence + other.sequence)

    def __truediv__(self, other):
        """Divide (``/``) this Result by another one."""
        return Result(self.concrete / other.concrete, self.symbolic / other.symbolic)

    def __repr__(self):
        return "({}, {}, {})".format(self.concrete, self.symbolic, self.sequence)

    def __iter__(self):
        return iter([self.concrete, self.symbolic])

    def clone(self):
        ret = Result(self.concrete, self.symbolic)
        ret.sequence = self.sequence
        return ret

    def add_seq_elem(self, elem):
        ret = self.clone()
        ret.sequence = ret.sequence + (elem,)
        return ret
