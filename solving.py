from z3 import *
import timeit

set_param("proof", "true")

def run_direct():
    pyname_i = Int("pyname_i")
    ret = Int("ret")
    x = Int("x")
    y = Int("y")
    conditioned = Function("conditioned", IntSort(), IntSort())
    run_func = Function("run_func", IntSort(), IntSort())
    s = Solver()
    s.add(
        ForAll(
            [pyname_i],
            Exists(
                [ret],
                And(
                    conditioned(pyname_i) == ret,
                    Or(And(pyname_i > 4, ret == 6), And(Not(pyname_i > 4), ret == 14)),
                ),
            ),
        )
    )
    # s.add(
    #     ForAll(
    #         [pyname_i],
    #         Exists(
    #             [ret],
    #             And(run_func(pyname_i) == ret, ret == pyname_i * conditioned(pyname_i)),
    #         ),
    #     )
    # )
    s.add(conditioned(34) == x)
    # s.add(run_func(2) == x)
    s.check()
    # print(s.model())

def run_function():
    pyname_i = Int("pyname_i")
    ret = Int("ret")
    x = Int("x")
    y = Int("y")
    conditioned = Function("conditioned", IntSort(), IntSort())
    run_func = Function("run_func", IntSort(), IntSort())
    s = Solver()

    s.add(ForAll([pyname_i], conditioned(pyname_i) == If(pyname_i > 4, 6, 14)))
    s.add(ForAll([pyname_i], run_func(pyname_i) == pyname_i * conditioned(pyname_i)))
    s.add(conditioned(34) == x)
    # s.add(run_func(2) == x)
    s.check()
    # print(s.model())

print("direct")
print(timeit.timeit("run_direct()", number=100, globals=globals()))
print("function")
print(timeit.timeit("run_function()", number=100, globals=globals()))
