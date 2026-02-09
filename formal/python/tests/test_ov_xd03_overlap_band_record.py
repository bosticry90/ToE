from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

from formal.python.toe.observables.ovxd03_overlap_band_record import ovxd03_overlap_band_record


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


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


def test_ov_xd03_overlap_band_record_math_and_lock_consistency():
    rec = ovxd03_overlap_band_record()

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-XD-03_cross_dataset_overlap_band_record.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    # Required baseline bands must exist; optional slots may be included later.
    band_keys = set(locked.get("bands", {}).keys())
    assert {"OV-01g", "OV-02x", "OV-03x"}.issubset(band_keys)

    # Inclusion bookkeeping must be consistent.
    assert set(locked.get("included_band_ids", [])) == band_keys
    excluded = locked.get("excluded", {})
    assert isinstance(excluded, dict)

    # Overlap definition checks (pure bookkeeping).
    bands = locked["bands"]

    # Overlap is the intersection across included bands.
    included = list(bands.keys())
    k_mins = [float(bands[k]["k_min"]) for k in included]
    k_maxs = [float(bands[k]["k_max"]) for k in included]

    expected_k_min = max(k_mins)
    expected_k_max = min(k_maxs)

    overlap = locked["overlap"]
    assert float(overlap["k_min"]) == pytest.approx(expected_k_min, abs=1e-12)
    assert float(overlap["k_max"]) == pytest.approx(expected_k_max, abs=1e-12)

    # Overlap max must not exceed any band max.
    for k in included:
        assert float(overlap["k_max"]) <= float(bands[k]["k_max"]) + 1e-12

    # Locked record must match current computed record (including fingerprint).
    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()
