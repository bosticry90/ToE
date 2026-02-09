from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovselbm01_benchmark_ingestion_stress_test_record import (
    ovselbm01_benchmark_ingestion_stress_test_record,
)


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


def test_ov_sel_bm01_lock_matches_computed_record_and_all_checks_pass() -> None:
    rec = ovselbm01_benchmark_ingestion_stress_test_record(status_date="2026-01-23")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-SEL-BM-01_benchmark_ingestion_stress_test.md"
    )
    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(text) == rec.fingerprint()

    checks = locked.get("checks") or {}
    assert checks
    assert all(bool(v.get("ok")) for v in checks.values())

    bms = locked.get("benchmarks") or {}
    assert bms.get("OV-BM-01", {}).get("non_decisive_by_design") is True
    assert bms.get("OV-BM-02", {}).get("non_decisive_by_design") is True
    assert bms.get("scope_fences", {}).get("no_curve_fitting") is True
    assert bms.get("scope_fences", {}).get("no_regime_averaging") is True
