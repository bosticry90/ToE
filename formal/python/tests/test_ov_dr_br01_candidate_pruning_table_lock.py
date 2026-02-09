from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import (
    ovdrbr01_candidate_pruning_table_record,
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


def test_ov_dr_br01_lock_matches_computed_record() -> None:
    rec = ovdrbr01_candidate_pruning_table_record(date="2026-01-25")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-DR-BR-01_candidate_pruning_table.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked["schema"] == "OV-DR-BR-01_candidate_pruning_table/v1"
    assert locked["observable_id"] == "OV-DR-BR-01"

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()


def test_ov_dr_br01_blocks_if_br05_missing() -> None:
    missing = REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "_MISSING_OV_BR_05_.md"
    rec = ovdrbr01_candidate_pruning_table_record(date="2026-01-25", br05_lock_path=missing)

    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_input_lock_OV-BR-05"]
    assert rec.rows == []

    assert rec.summary["counts"] == {"true": 0, "false": 0, "unknown": 0}
    assert rec.summary["candidates"] == {"true": [], "false": [], "unknown": []}


def test_ov_dr_br01_blocks_if_pred_decl_lock_missing() -> None:
    missing = REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "_MISSING_OV_DR_BR_00_.md"
    rec = ovdrbr01_candidate_pruning_table_record(date="2026-01-25", pred_decl_lock_path=missing)

    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_input_lock_OV-DR-BR-00"]
    assert rec.rows == []

    assert rec.summary["counts"] == {"true": 0, "false": 0, "unknown": 0}
    assert rec.summary["candidates"] == {"true": [], "false": [], "unknown": []}


def test_ov_dr_br01_schema_complete_in_all_code_paths() -> None:
    # Schema completeness invariant: all code paths must return a record that includes
    # a usable summary rollup (even when blocked by missing inputs).
    ok = ovdrbr01_candidate_pruning_table_record(date="2026-01-25")
    assert set(ok.summary.keys()) == {"counts", "candidates"}
    assert set(ok.summary["counts"].keys()) == {"true", "false", "unknown"}
    assert set(ok.summary["candidates"].keys()) == {"true", "false", "unknown"}

    missing_br05 = REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "_MISSING_OV_BR_05_.md"
    blocked1 = ovdrbr01_candidate_pruning_table_record(date="2026-01-25", br05_lock_path=missing_br05)
    assert set(blocked1.summary.keys()) == {"counts", "candidates"}

    missing_pred = REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "_MISSING_OV_DR_BR_00_.md"
    blocked2 = ovdrbr01_candidate_pruning_table_record(date="2026-01-25", pred_decl_lock_path=missing_pred)
    assert set(blocked2.summary.keys()) == {"counts", "candidates"}
