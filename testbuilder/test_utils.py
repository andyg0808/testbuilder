from typing import Sequence
def write_dot(lines: Sequence[str], filename: str) -> None:
    print("Writing dot to", filename)
    with open(filename, "w") as f:
        data = "\n".join(lines)
        formatted = """
digraph G {{
{}
}}
        """.format(
            data
        )
        f.write(formatted)
