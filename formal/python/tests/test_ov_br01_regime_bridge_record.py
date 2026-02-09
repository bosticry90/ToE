from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

from formal.python.toe.observables.ovbr01_regime_bridge_record import ovbr01_regime_bridge_record


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _extract_block(text: str, *, block_id: str) -> str:
    marker_re = re.compile(rf"^ID:\s*{re.escape(block_id)}\s*$", flags=re.MULTILINE)
    m = marker_re.search(text)
    if m is None:
        raise AssertionError(f"Could not find exact block marker for ID: {block_id!r}")
    start = m.start()

    next_idx = text.find("\n\n\nID:", start + 1)
    if next_idx < 0:
        return text[start:]
    return text[start:next_idx]


def _first_field(block: str, field: str) -> str | None:
    prefix = f"{field}:"
    for line in block.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise AssertionError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise AssertionError("Missing record fingerprint line")
    return m.group(1)


def test_ov_br01_inventory_wiring_and_scope_guardrails():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    block = _extract_block(doc, block_id="OV-BR-01")

    assert _first_field(block, "Category") == "Observable"

    deps = _first_field(block, "Dependencies") or ""
    for required in ["OV-01g", "OV-03x", "OV-XD-03"]:
        assert required in deps

    scope = (_first_field(block, "Scope / limits") or "").lower()

    assert "separately" in scope
    assert "no averaging" in scope
    assert "no continuity claim" in scope


def test_ov_br01_lock_exists_and_matches_computed_record():
    rec = ovbr01_regime_bridge_record()

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-01_regime_bridge_record.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    # Required operational fields.
    assert "low_band" in locked
    assert "high_band" in locked

    # Overlap-or-explicit-no-overlap rule.
    overlap = locked.get("overlap")
    if overlap is None:
        lower = lock_text.lower()
        assert "no overlap" in lower
        assert ("comparison is not valid" in lower) or ("comparison not valid" in lower)
    else:
        assert isinstance(overlap, list) and len(overlap) == 2
        assert float(overlap[1]) >= float(overlap[0])

        low = locked["low_band"]
        high = locked["high_band"]
        expected_min = max(float(low[0]), float(high[0]))
        expected_max = min(float(low[1]), float(high[1]))
        assert float(overlap[0]) == pytest.approx(expected_min, abs=1e-12)
        assert float(overlap[1]) == pytest.approx(expected_max, abs=1e-12)

    # Locked record must match current computed record (including fingerprint).
    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()
