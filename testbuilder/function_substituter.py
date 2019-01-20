from typing import Any, Generator, List, Optional

import dataclasses

from . import nodetree as n, ssa_basic_blocks as sbb
from .variable_manager import VAR_START_VALUE
from .visitor import CoroutineVisitor, UpdateVisitor


class FunctionSubstitute(UpdateVisitor):
    """Finds function calls and replaces them with the function
    definition.
    """

    def __init__(self) -> None:
        super().__init__()
        self.call_id = 0

    def visit_Request(self, request: sbb.Request) -> sbb.Request:
        code = self.generic_visit(request.code, module=request.module)
        return dataclasses.replace(request, code=code)

    def visit_Code(
        self, node: sbb.Code, start_line: int = 0, **kwargs: Any
    ) -> sbb.BasicBlock:
        lines = list(enumerate(node.code[start_line:]))
        for num, line in reversed(lines):
            calls = find_calls(line)
            if calls:
                # This seems like a restriction that shouldn't be needed
                assert len(calls) == 1
                return self.split_code(node, num + start_line, calls[0], **kwargs)
        # If there are no function calls here, move on to the parent node.
        return self.generic_visit(node, **kwargs)

    def split_code(
        self, node: sbb.Code, num: int, call: n.Call, **kwargs: Any
    ) -> sbb.BasicBlock:
        def build_block(
            lines: List[n.stmt], first_line: int, parent: sbb.BasicBlock
        ) -> sbb.Code:
            return sbb.Code(
                number=node.number,
                first_line=first_line,
                last_line=first_line + len(lines),
                parent=parent,
                code=lines,
            )

        name = get_function_name(call.func)
        call_info = n.Prefix(func=name.id, number=self.next_id())

        parent = node.parent
        func = kwargs["module"].functions.get(call_info.func, None)
        if not func:
            return self.visit(node, num + 1, **kwargs)

        argument_bindings = bind_arguments(call_info, call, func, num)
        first_lines = node.code[:num] + argument_bindings

        if first_lines:
            parent = build_block(first_lines, node.first_line, parent)
        parent = self.visit(parent, **kwargs)

        parent = self.fetch_function(call_info, call, func, parent)

        return_binding = self.visit(node.code[num], call_info, **kwargs)
        if return_binding:
            last_lines = [return_binding] + node.code[num + 1 :]
        else:
            last_lines = node.code[num + 1 :]
        if last_lines:
            parent = build_block(last_lines, node.first_line + num + 1, parent)
        return parent

    def fetch_function(
        self,
        call_info: n.Prefix,
        call: n.Call,
        func: sbb.FunctionDef,
        parent: sbb.BasicBlock,
    ) -> sbb.BasicBlock:
        print("reparenting")
        prefixer = VariablePrefix()
        prefixed: sbb.BasicBlock = prefixer(func.blocks.end, call_info)
        reparent = Reparent()
        reparented = reparent.visit(prefixed, parent)
        return reparented

    def next_id(self) -> int:
        self.call_id += 1
        return self.call_id

    def visit_Expr(
        self, expr: n.Expr, call_info: Optional[n.Prefix] = None, **kwargs: Any
    ) -> Optional[n.Expr]:
        if not call_info:
            return self.generic_visit(expr, **kwargs)
        if isinstance(expr.value, n.Call):
            # Discard call sites which are for side-effects only
            return None
        return self.generic_visit(expr, call_info, **kwargs)

    def visit_Call(
        self, call: n.Call, call_info: Optional[n.Prefix] = None, **kwargs: Any
    ) -> n.expr:
        # If a call_info is passed, we want to substitute the
        # call. Otherwise, leave it alone.
        if call_info:
            return n.Result(func=call_info.func, number=call_info.number)
        else:
            return self.generic_visit(call, **kwargs)


class Reparent(UpdateVisitor):
    def visit_StartBlock(
        self, block: sbb.StartBlock, swap: Optional[sbb.BasicBlock]
    ) -> sbb.BasicBlock:
        if swap:
            return swap
        return block


def get_function_name(func: n.expr) -> n.Name:
    assert isinstance(
        func, n.Name
    ), "No support for functions which aren't in variables"
    return func


def find_calls(node: n.Node) -> List[n.Call]:
    finder = CallFinder()
    calls = [f for f in finder(node) if f]
    return calls


def bind_arguments(
    call_info: n.Prefix, call: n.Call, func: sbb.FunctionDef, line: int
) -> List[n.stmt]:
    def bind_arg(formal_param: str, value: n.expr) -> n.ArgumentBind:
        name = n.PrefixedName(
            func=call_info.func,
            number=call_info.number,
            id=formal_param,
            set_count=VAR_START_VALUE,
        )
        return n.ArgumentBind(line=line, target=name, e=value)

    assert len(call.args) == len(func.args)
    return [bind_arg(*arg) for arg in zip(func.args, call.args)]


class CallFinder(CoroutineVisitor[n.Call, None]):
    def visit_Call(self, node: n.Call) -> Generator[n.Call, None, None]:
        yield node


class VariablePrefix(UpdateVisitor):
    def visit_Name(self, name: n.Name, prefix: n.Prefix) -> n.PrefixedName:
        return n.PrefixedName(
            id=name.id, set_count=name.set_count, func=prefix.func, number=prefix.number
        )

    def visit_Return(self, ret: n.Return, prefix: n.Prefix) -> n.ReturnResult:
        return n.ReturnResult(
            line=ret.line,
            value=self.visit(ret.value, prefix),
            func=prefix.func,
            number=prefix.number,
        )
