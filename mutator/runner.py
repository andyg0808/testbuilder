import os
from abc import ABC, abstractmethod
from pathlib import Path
from subprocess import DEVNULL, CompletedProcess, run
from tempfile import TemporaryDirectory
from typing import Generic, List, TypeVar

A = TypeVar("A")


class Runner(Generic[A], ABC):
    def __init__(self, base: Path, target_name: str, testrunner: List[str]) -> None:
        self.target_name = target_name
        self.testrunner = testrunner
        self.base = base
        # Seconds to wait for completion
        self.timeout = 60

    def run_test(self, variant: A) -> CompletedProcess:
        """
        Executes a specific variant
        """
        with TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            self.setup_base(tmp_path)
            self.get_variant(variant, tmp_path / self.target_name)
            orig = os.getcwd()
            os.chdir(tmp)
            try:
                return self.run()
            finally:
                os.chdir(orig)

    def setup_base(self, dest: Path) -> None:
        if run(["cp", "-r", self.base, dest]).returncode != 0:
            raise RuntimeError("rsync failed")

    @abstractmethod
    def get_variant(self, variant: A, dest: Path) -> None:
        ...

    def run(self) -> CompletedProcess:
        result = run(self.testrunner, stdout=DEVNULL, timeout=self.timeout)
        print(".", end="")
        return result
