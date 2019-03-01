import ast
from compiler import compiler
from importlib.machinery import ModuleSpec
from importlib.util import module_from_spec


def test_code_compilation():
    """Test the basic case: can we load this module and will it deserialize
    correctly?"""
    code = """
class Fish:
    def __init__(self):
        self.fish_count = 4
        self.fish_length = 46.8

    def total_length(self):
        return self.fish_count * self.fish_length
        """
    tree = ast.parse(code)
    module = compiler(tree)
    assert isinstance(module, str)

    spec = ModuleSpec("fish", None)
    loaded = module_from_spec(spec)
    print(module)
    exec(module, loaded.__dict__)

    expected = module_from_spec(spec)
    exec(code, expected.__dict__)

    loaded_fish = loaded.Fish()
    expected_fish = expected.Fish()

    assert loaded_fish.total_length() == expected_fish.total_length()
