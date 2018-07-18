"""Tool to run concolic testing on a module."""

import ast
import random
import re
import sys
from unittest import TestCase

import astor
from termcolor import cprint

import z3

# import IPython
from . import method_env_2, utils
from .result import Result
from .symb_util import Symbolics


class Tester(TestCase):
    """Runs concolic testing on a file."""

    def __init__(self):
        self.symb = Symbolics()

    def run_code(self, function):
        pass

    def _print_source(self, func):
        # print(astor.dump_tree(func))
        # utils.print_locations(func)
        print(astor.to_source(func))

    def main(self, argv):
        """Run tests on passed argument."""
        z3.set_param(proof=True)
        fut = argv[1]
        with open(fut) as fh:
            data = fh.read()
            module = ast.parse(data, fut)

            # self._print_source(module)

            annotated = method_env_2.AnnotateModule().visit(module)
            annotated = ast.fix_missing_locations(annotated)

            self._print_source(annotated)

            c = compile(annotated, "<string>", "exec")
            g = {}
            r = exec(c, g)

            for thing in module.body:
                if isinstance(thing, ast.FunctionDef):
                    self._test(thing, g[thing.name])

    def _test(self, defn, function):
        """Run concolic testing on a single function.


        If an expectation line is included, also checks that the
        output of the function is sane.

        """
        print("Testing {}...".format(defn.name))
        expectations = self._getExpect(defn)
        if expectations:
            for expected in expectations:
                print("Running {} with {}...".format(defn.name, expected["input"]))
                ret = function(*self._build_args(expected["input"], defn))
                result = Result(*ret)
                print(result.concrete, expected["concrete"])
                self.assertEqual(result.concrete, expected["concrete"])
            print("{} result: {}".format(defn.name, result))
            print("Simplified: {}".format(z3.simplify(result.symbolic)))
            cprint("✔ All provided examples pass!", "green")
        else:
            cprint(
                "No expectation found for {}. \ue22f  Generating random inputs...".format(
                    defn.name
                ),
                "blue",
            )
            ret = function(*self._build_args([], defn))
            result = Result(*ret)
        tries = self._find_new_args(result)
        while len(tries) > 0:
            depth, values = tries.pop()
            ret = function(*self._build_args(values, defn))
            result = Result(*ret)
            print("values", values)
            tries += self._find_new_args(result, depth)
            print("Found another: {}".format(result))

        print("{} is not broken".format(defn.name))

    def _build_args(self, arg_values, defn):
        arguments = defn.args
        arg_names = map(lambda arg: arg.arg, arguments.args)
        arg_list = []
        for i, name in enumerate(arg_names):
            if arg_values and name in arg_values:
                arg_list.append(arg_values[name])
            elif arg_values and i < len(arg_values):
                arg_list.append(arg_values[i])
            else:
                # Take type into account here
                arg_list.append(random.random())
        cprint(arg_list, "blue")
        return arg_list

    def _find_new_args(self, result, start=0):
        routes = self._gather_alternate_routes(result.sequence, start)
        arg_groups = []
        for route in routes:
            s = z3.Solver()
            for cond in route:
                s.add(cond)
            res = s.check()
            if res == z3.sat:
                model = s.model()
                arg_groups.append((len(route), self.model_to_args(model)))
                print("Found another route!")
        return arg_groups

    def model_to_args(self, model):
        ret = {}
        decls = (str(n) for n in model.decls())
        for name in decls:
            print(name)
            ret[name] = self.symb.z3_to_python(
                model.get_interp(z3.Const(name, self.symb.obj_sort))
            )
        return ret

    def _gather_alternate_routes(self, seq, start):
        """Returns a list of other arguments to try."""
        res = []
        cprint("seq: {}; start: {}".format(seq, start), "magenta")
        partial = list(seq[:start])
        cprint("partial: {}".format(partial), "magenta")
        for i in seq[start:]:
            bool_i = self.symb.z3_to_bool(i)
            print(bool_i)
            res.append(partial + [z3.Not(bool_i)])
            partial.append(i)
            cprint("partial: {}".format(partial), "magenta")
        return res

    def _getExpect(self, function):
        flag = re.compile("^\\s*Expect:\\s+(.*)$", re.IGNORECASE | re.MULTILINE)
        docstring = ast.get_docstring(function)
        if docstring:
            matches = flag.finditer(docstring)
            results = []
            for match in matches:
                expectation = match.group(1)
                expectation_ast = ast.parse(expectation, "<string>", "eval")
                inputs, conc_output = expectation_ast.body.elts
                input_values = compile(ast.Expression(inputs), "<string>", "eval")
                input_requirement = eval(input_values)
                conc_expectation = eval(
                    compile(ast.Expression(conc_output), "<string>", "eval")
                )
                results.append(
                    {"input": input_requirement, "concrete": conc_expectation}
                )
            if len(results) > 0:
                return results


if __name__ == "__main__":
    t = Tester()
    t.main(sys.argv)
