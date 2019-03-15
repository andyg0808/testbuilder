import builtins
import os
import sys
from pathlib import Path

root = Path(__file__).parent
binary = Path(os.environ.get("Z3_LIBRARY_PATH", root / "z3_source" / "build"))

builtins.Z3_LIB_DIRS = [binary]
sys.path.append(str(binary / "python"))

if os.environ.get("Z3_ROOT_PRINT", False):
    print(builtins.Z3_LIB_DIRS)
