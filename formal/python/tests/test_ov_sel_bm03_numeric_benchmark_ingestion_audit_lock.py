from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovselbm03_numeric_benchmark_ingestion_audit_ovbm02n_record import (
    ovselbm03_numeric_benchmark_ingestion_record,
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


def test_ov_sel_bm03_lock_matches_computed_record() -> None:
    rec = ovselbm03_numeric_benchmark_ingestion_record(status_date="2026-01-24")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-SEL-BM-03_numeric_benchmark_ingestion_audit_OV-BM-02N.md"
    )

    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(text) == rec.fingerprint()

    assert locked["benchmark_numeric"]["digitization_id"] == "OV-BM-02N"

    csv_rel = locked["benchmark_numeric"]["csv_relpath"]
    assert (REPO_ROOT / csv_rel).exists()
