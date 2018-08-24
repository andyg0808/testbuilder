import ast

import pytest

from . import ast_builder as ab, nodetree as n


def check_expr(code: str, expected: n.expr):
    # check_stmt(code, n.Expr(line=1, value=expected))
    check_ast(code, expected);


# def check_stmt(code: str, expected: n.stmt):
#     check_ast(code, n.Module([expected]))


def check_ast(code: str, expected: n.Node):
    tree = ast.parse(code).body[0].value
    print('tree', tree)
    builder = ab.AstBuilder({})
    tree = builder.visit(tree)
    assert tree == expected


def test_build_int_ast():
    check_expr("1", n.Int(1))


def test_build_str_ast():
    check_expr("'abc'", n.Str("abc"))


# def test_build_int_assign():
#     check_stmt("a = 1", n.Set(n.Name("a", 0), n.Int(1)))


def test_build_call():
    check_expr("f(1, 2)", n.Call(n.Name("f", 0), [n.Int(1), n.Int(2)], []))


# @pytest.mark.skip
# def test_build_array_assign():
#     check_stmt("a[0] = 1", n.Set(n.Name("a", 1), n.Store(n.Name("a", 0), 0, n.Int(1))))
