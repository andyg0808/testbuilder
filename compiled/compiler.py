"""
Self-deserializing bytecode modules

compiler allows us to compile and serialize a Python module into a
self-deserializing module file. The module file will execute Python when loaded
which will delete all the contents of its `__dict__` and replace them with the
equivalent of the serialized module.
"""
import ast
import marshal


def compiler(module: ast.Module):
    """
    Creates a serialized version of a Python module which will self-deserialize
    when loaded.
    """
    assert isinstance(module, ast.Module)
    code = compile(module, "<module>", "exec")
    dump = marshal.dumps(code)
    binstring = repr(dump)
    return f"""
def __load__():
    from marshal import loads
    globs = globals()
    globs.clear()
    module = loads({binstring})
    exec(module, globs)
__load__()
"""
