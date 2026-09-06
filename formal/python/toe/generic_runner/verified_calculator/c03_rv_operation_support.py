"""Closed support primitives for the trusted C03/RV operation vocabulary.

This module deliberately contains no imports from the historical runner tree.
It provides only bounded exact parsing, structural equality, and the one
domain-neutral normalization primitive used by the migrated profile operations.
"""
from __future__ import annotations

import ast
import re
from typing import Any

import sympy as sp

from .errors import CalculatorError, require as _require


VerificationError = CalculatorError


def require(condition: bool, code: str, detail: str = "") -> None:
    _require(condition, code, detail=detail)


def exact_expr(value: Any) -> sp.Basic:
    """Parse the profile's rational-function grammar without host evaluation."""
    require(type(value) in (int, str), "C03_RV_EXACT_SCALAR_REQUIRED")
    text = str(value).replace("^", "**")
    require(0 < len(text) <= 2_048, "C03_RV_EXACT_SCALAR_SIZE")
    try:
        tree = ast.parse(text, mode="eval")
    except (SyntaxError, ValueError) as exc:
        raise CalculatorError("C03_RV_EXACT_SCALAR_SYNTAX") from exc
    require(sum(1 for _ in ast.walk(tree)) <= 256, "C03_RV_EXACT_SCALAR_AST")

    def visit(node: ast.AST) -> sp.Basic:
        if isinstance(node, ast.Constant) and type(node.value) is int:
            require(abs(node.value).bit_length() <= 256, "C03_RV_INTEGER_SIZE")
            return sp.Integer(node.value)
        if isinstance(node, ast.Name):
            require(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", node.id) is not None, "C03_RV_SYMBOL")
            return sp.I if node.id == "I" else sp.Symbol(node.id)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value = visit(node.operand)
            return value if isinstance(node.op, ast.UAdd) else -value
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "sqrt" and len(node.args) == 1 and not node.keywords:
            radicand = visit(node.args[0])
            require(radicand.is_Integer is True and 0 < radicand <= 100, "C03_RV_RADICAL_ARGUMENT")
            return sp.sqrt(radicand)
        if isinstance(node, ast.BinOp):
            left, right = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
            if isinstance(node.op, ast.Div):
                require(right != 0, "C03_RV_ZERO_DENOMINATOR")
                return left / right
            if isinstance(node.op, ast.Pow):
                require(right.is_Integer is True and abs(int(right)) <= 32, "C03_RV_POWER_DOMAIN")
                require(not (left == 0 and right < 0), "C03_RV_ZERO_DENOMINATOR")
                return left ** right
        raise CalculatorError("C03_RV_EXACT_CAPABILITY", detail=type(node).__name__)

    result = sp.cancel(visit(tree.body))
    require(not result.has(sp.zoo, sp.nan, sp.oo, -sp.oo), "C03_RV_NONFINITE_EXACT_VALUE")
    return result


def exact_equal(left: Any, right: Any) -> bool:
    if isinstance(left, sp.MatrixBase) or isinstance(right, sp.MatrixBase):
        return isinstance(left, sp.MatrixBase) and isinstance(right, sp.MatrixBase) and left.shape == right.shape and all(exact_equal(a, b) for a, b in zip(left, right))
    if isinstance(left, (tuple, list)) or isinstance(right, (tuple, list)):
        return isinstance(left, (tuple, list)) and isinstance(right, (tuple, list)) and len(left) == len(right) and all(exact_equal(a, b) for a, b in zip(left, right))
    if isinstance(left, dict) or isinstance(right, dict):
        return isinstance(left, dict) and isinstance(right, dict) and set(left) == set(right) and all(exact_equal(left[key], right[key]) for key in left)
    if isinstance(left, sp.Basic) or isinstance(right, sp.Basic):
        try:
            return sp.cancel(sp.sympify(left) - sp.sympify(right)) == 0
        except (TypeError, ValueError):
            return False
    return type(left) is type(right) and left == right


def arithmetic(operation: str, parents: list[Any]) -> Any:
    require(operation == "INVERTIBLE_NORMALIZATION" and len(parents) == 3, "C03_RV_NORMALIZATION_SIGNATURE")
    value, scale, inverse = parents
    require(scale != 0 and inverse != 0 and sp.cancel(scale * inverse - 1) == 0, "C03_RV_NORMALIZATION_INVERSE")
    return sp.cancel(value * scale)
