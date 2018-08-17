import subprocess
from functools import partial, singledispatch
from logging import Logger
from types import MappingProxyType
from typing import (
    Any,
    Callable,
    List,
    Mapping,
    MutableMapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from . import ssa_basic_blocks as sbb
from .ssa_formatter import format_tree

log = Logger("test_utils")


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
    log.debug("Writing dot to", filename)
    with open(filename, "w") as f:
        formatted = format_dot(lines)
        f.write(formatted)


@singledispatch
def show_dot(obj: Any) -> None:
    lines = dotify(obj)
    log.debug("Showing dot of", lines)
    show_dot(lines)


@show_dot.register(list)
def show_dot_from_lines(lines: Sequence[str]) -> None:
    formatted = format_dot(lines)
    subprocess.run(["dot", "-Tx11"], input=formatted.encode())


Lister = Callable[[Any], List[str]]
DotList = List[str]


LabelData = Union[Tuple[str, Mapping[str, Any]], str, Mapping[str, Any]]

EmptyDict: Mapping[str, Any] = MappingProxyType({})


def dotify(obj: Any, reverse: bool = False) -> List[str]:
    node_strings = []
    link_strings = []
    nodes = [obj]
    seen: Set[Any] = set()
    while len(nodes) > 0:
        node = nodes.pop(0)
        if id(node) in seen:
            next
        seen.add(id(obj))
        node_strings.append(_label_format(node, _dot_label(node)))
        next_nodes = nexts(node)
        for n in next_nodes:
            if reverse:
                link = f"{id(n)} -> {id(node)};"
            else:
                link = f"{id(node)} -> {id(n)};"
            link_strings.append(link)
            nodes.append(n)
    return node_strings + link_strings


def _label_format(obj: Any, data: LabelData) -> str:
    if isinstance(data, tuple):
        label, args = data
    elif isinstance(data, Mapping):
        args = data
        label = ""
    else:
        args = {}
        label = data
    arg_list = args.items() | {"label": label}.items()
    args_string = ",".join(f'{k}="{v}"' for k, v in arg_list)
    return f"{id(obj)}[{args_string}];"


@singledispatch
def _dot_label(obj: object) -> LabelData:
    raise RuntimeError(f"`dot` formatting not implemented for {type(obj)}")


@_dot_label.register(sbb.BasicBlock)
def _dot_label_basic_block(block: sbb.BasicBlock) -> LabelData:
    return {"xlabel": block.number}


@_dot_label.register(sbb.Code)
def _dot_label_code_block(block: sbb.Code) -> LabelData:
    body = "\n".join(format_tree(c) for c in block.code)
    return (body, {"xlabel": block.number})


@singledispatch
def nexts(obj: object) -> List[Any]:
    raise RuntimeError(f"No nexts implementation for {type(obj)}")


@nexts.register(sbb.Code)
def nexts_code(obj: sbb.Code) -> List[Any]:
    return [obj.parent]


@nexts.register(sbb.Loop)
def nexts_loop(obj: sbb.Loop) -> List[Any]:
    return [obj.loop_branch, obj.bypass]


@nexts.register(sbb.BasicBlock)
def nexts_block(obj: sbb.BasicBlock) -> List[Any]:
    return []
