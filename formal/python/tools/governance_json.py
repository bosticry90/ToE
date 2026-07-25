"""Strict current-authority and forensic historical JSON readers."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Iterable


class DuplicateKeyError(ValueError):
    """Current authority JSON contains an ambiguous object member."""


class PairObject:
    """An ordered object representation that deliberately is not a mapping."""

    __slots__ = ("pairs",)

    def __init__(self, pairs: Iterable[tuple[str, Any]]) -> None:
        self.pairs = tuple(pairs)


class ForensicJsonDocument:
    """Byte-preserving historical parse with duplicate reporting only."""

    __slots__ = ("raw_bytes", "raw_sha256", "root", "duplicates")

    def __init__(
        self,
        raw_bytes: bytes,
        root: Any,
        duplicates: tuple[dict[str, Any], ...],
    ) -> None:
        self.raw_bytes = raw_bytes
        self.raw_sha256 = hashlib.sha256(raw_bytes).hexdigest()
        self.root = root
        self.duplicates = duplicates


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def strict_current_authority_loads(raw: bytes | str) -> Any:
    """Parse a current decision-bearing JSON value and reject duplicates."""

    if isinstance(raw, bytes):
        text = raw.decode("utf-8")
    else:
        text = raw
    return json.loads(text, object_pairs_hook=_strict_object)


def strict_current_authority_parse(path: Path) -> Any:
    return strict_current_authority_loads(path.read_bytes())


def _forensic_object(pairs: list[tuple[str, Any]]) -> PairObject:
    return PairObject(pairs)


def _fingerprint(value: Any) -> str:
    if isinstance(value, PairObject):
        serializable = {
            "__ordered_pairs__": [
                [key, _fingerprint(child)] for key, child in value.pairs
            ]
        }
    elif isinstance(value, list):
        serializable = [_fingerprint(child) for child in value]
    else:
        serializable = value
    encoded = json.dumps(
        serializable,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _duplicate_reports(value: Any, path: str = "$") -> list[dict[str, Any]]:
    reports: list[dict[str, Any]] = []
    if isinstance(value, PairObject):
        grouped: dict[str, list[Any]] = {}
        for key, child in value.pairs:
            grouped.setdefault(key, []).append(child)
        for key, values in grouped.items():
            if len(values) > 1:
                reports.append(
                    {
                        "json_path": path,
                        "key": key,
                        "occurrences": len(values),
                        "value_fingerprints": [_fingerprint(item) for item in values],
                    }
                )
        occurrence: dict[str, int] = {}
        for key, child in value.pairs:
            index = occurrence.get(key, 0)
            occurrence[key] = index + 1
            child_path = f"{path}.{key}[{index}]"
            reports.extend(_duplicate_reports(child, child_path))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reports.extend(_duplicate_reports(child, f"{path}[{index}]"))
    return reports


def forensic_historical_parse_bytes(raw: bytes) -> ForensicJsonDocument:
    root = json.loads(raw.decode("utf-8"), object_pairs_hook=_forensic_object)
    return ForensicJsonDocument(raw, root, tuple(_duplicate_reports(root)))


def forensic_historical_parse(path: Path) -> ForensicJsonDocument:
    return forensic_historical_parse_bytes(path.read_bytes())
