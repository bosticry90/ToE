"""Canonical wire encoding for exact profile ledgers and source contexts.

This is a domain-neutral serialization primitive shared by proposal and
verification routes.  It performs no physics calculation.
"""
from __future__ import annotations

from typing import Any, Mapping

import sympy as sp

from .canonical import canonical_data
from .errors import CalculatorError, require
from . import c03_rv_operation_support as support


def encode_profile_value(value: Any) -> dict[str, Any]:
    if value is None:
        return {"type": "NULL"}
    if type(value) is bool:
        return {"type": "BOOLEAN", "value": value}
    if type(value) is int:
        return {"type": "INTEGER", "value": value}
    if isinstance(value, sp.MatrixBase):
        return {"type": "MATRIX", "rows": value.rows, "columns": value.cols, "entries": [encode_profile_value(value[row, column]) for row in range(value.rows) for column in range(value.cols)]}
    # Immutable SymPy matrices are also Basic objects.  Matrix must therefore
    # be dispatched first so mutable and immutable exact matrices have one
    # canonical wire representation.
    if isinstance(value, sp.Basic):
        return {"type": "EXACT_EXPRESSION", "value": sp.sstr(sp.cancel(value))}
    if isinstance(value, str):
        return {"type": "TEXT", "value": value}
    if isinstance(value, tuple):
        return {"type": "TUPLE", "items": [encode_profile_value(item) for item in value]}
    if isinstance(value, list):
        return {"type": "LIST", "items": [encode_profile_value(item) for item in value]}
    if isinstance(value, Mapping):
        require(all(isinstance(key, str) for key in value), "PROFILE_VALUE_MAP_KEY")
        return {"type": "MAP", "entries": [[key, encode_profile_value(value[key])] for key in sorted(value)]}
    raise CalculatorError("PROFILE_VALUE_TYPE", detail=type(value).__name__)


def decode_profile_value(value: Mapping[str, Any]) -> Any:
    require(isinstance(value, Mapping) and isinstance(value.get("type"), str), "PROFILE_VALUE_SCHEMA")
    kind = value["type"]
    if kind == "NULL":
        require(set(value) == {"type"}, "PROFILE_VALUE_SCHEMA")
        return None
    if kind == "BOOLEAN":
        require(set(value) == {"type", "value"} and type(value["value"]) is bool, "PROFILE_VALUE_SCHEMA")
        return value["value"]
    if kind == "INTEGER":
        require(set(value) == {"type", "value"} and type(value["value"]) is int and abs(value["value"]).bit_length() <= 16_384, "PROFILE_VALUE_SCHEMA")
        return value["value"]
    if kind == "EXACT_EXPRESSION":
        require(set(value) == {"type", "value"}, "PROFILE_VALUE_SCHEMA")
        return support.exact_expr(value["value"])
    if kind == "TEXT":
        require(set(value) == {"type", "value"} and isinstance(value["value"], str) and len(value["value"]) <= 65_536, "PROFILE_VALUE_SCHEMA")
        return value["value"]
    if kind in {"LIST", "TUPLE"}:
        require(set(value) == {"type", "items"} and isinstance(value["items"], list) and len(value["items"]) <= 262_144, "PROFILE_VALUE_SCHEMA")
        items = [decode_profile_value(item) for item in value["items"]]
        return tuple(items) if kind == "TUPLE" else items
    if kind == "MAP":
        require(set(value) == {"type", "entries"} and isinstance(value["entries"], list), "PROFILE_VALUE_SCHEMA")
        result: dict[str, Any] = {}
        for row in value["entries"]:
            require(isinstance(row, list) and len(row) == 2 and isinstance(row[0], str) and row[0] not in result, "PROFILE_VALUE_MAP_ENTRY")
            result[row[0]] = decode_profile_value(row[1])
        return result
    if kind == "MATRIX":
        require(set(value) == {"type", "rows", "columns", "entries"} and type(value["rows"]) is int and type(value["columns"]) is int and 0 < value["rows"] <= 262_144 and 0 < value["columns"] <= 262_144, "PROFILE_VALUE_SCHEMA")
        require(value["rows"] * value["columns"] == len(value["entries"]) <= 262_144, "PROFILE_VALUE_MATRIX_SIZE")
        entries = [decode_profile_value(item) for item in value["entries"]]
        return sp.ImmutableMatrix(value["rows"], value["columns"], entries)
    raise CalculatorError("PROFILE_VALUE_KIND", detail=kind)


def wrapped_profile_value(value: Any) -> dict[str, Any]:
    result = {"kind": "PROFILE_VALUE", "value": encode_profile_value(value)}
    canonical_data(result)
    return result


def unwrap_profile_value(value: Mapping[str, Any]) -> Any:
    require(set(value) == {"kind", "value"} and value["kind"] == "PROFILE_VALUE", "PROFILE_VALUE_WRAPPER")
    return decode_profile_value(value["value"])
