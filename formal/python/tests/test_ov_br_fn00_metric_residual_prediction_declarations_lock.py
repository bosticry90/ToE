from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovbrfn00_fn01_metric_residual_prediction_declarations_record import (
    ovbrfn00_metric_residual_prediction_declarations_record,
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


def test_ov_br_fn00_lock_matches_computed_record() -> None:
    rec = ovbrfn00_metric_residual_prediction_declarations_record(date="2026-01-25")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-FN-00_fn01_metric_residual_prediction_declarations.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked["schema"] == "OV-BR-FN-00_fn01_metric_residual_prediction_declarations/v1"
    assert locked["observable_id"] == "OV-BR-FN-00"

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()


def test_ov_br_fn00_blocks_if_source_missing() -> None:
    missing = REPO_ROOT / "formal" / "python" / "toe" / "bridges" / "_MISSING_BRFN_PRED_DECL_.json"
    rec = ovbrfn00_metric_residual_prediction_declarations_record(date="2026-01-25", declarations_path=missing)

    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_prediction_declarations_source"]
    assert rec.rows == []
