import ast
from termcolor import cprint


def print_locations(node):
    for i in ast.walk(node):
        if not hasattr(i, "lineno") or not hasattr(i, "col_offset"):
            cprint(i, "red")
        else:
            print(
                "{} line={} col={}".format(
                    i, getattr(i, "lineno", "none"), getattr(i, "col_offset", "none")
                )
            )


def crash(reason: str = ""):
    if reason:
        raise RuntimeError("Crashing because" + reason)
    raise RuntimeError("Crashing!")
