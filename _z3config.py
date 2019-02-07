import builtins
import os
from pathlib import Path

root = Path(__file__).parent

builtins.Z3_LIB_DIRS = [root / "z3_source" / "build"]

if os.environ.get("Z3_ROOT_PRINT", False):
    print(builtins.Z3_LIB_DIRS)
