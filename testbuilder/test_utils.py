import subprocess
from typing import Sequence


def format_dot(lines: Sequence[str]) -> str:
    data = "\n".join(lines)
    formatted = """
digraph G {{
{}
}}
        """.format(
        data
    )
    return formatted


def write_dot(lines: Sequence[str], filename: str) -> None:
    print("Writing dot to", filename)
    with open(filename, "w") as f:
        formatted = format_dot(lines)
        f.write(formatted)


def show_dot(lines: Sequence[str]) -> None:
    formatted = format_dot(lines)
    subprocess.run(["dot", "-Tx11"], input=formatted.encode())
