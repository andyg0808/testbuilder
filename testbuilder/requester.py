import readline

# From rlcompleter docs. This import is magical, so we don't care that
# it's unused.
import rlcompleter  # noqa: F401

from pygments import highlight  # type: ignore
from pygments.formatters import TerminalFormatter  # type: ignore
from pygments.lexers import PythonLexer  # type: ignore

readline.parse_and_bind("tab: complete")


Lexer = PythonLexer()
Formatter = TerminalFormatter()


class Requester:
    def input(self, prompt: str = "") -> str:
        return input(prompt)

    def formatted_output(self, s: str) -> None:
        self.output(highlight(s, Lexer, Formatter))

    def output(self, s: str) -> None:
        print(s)
