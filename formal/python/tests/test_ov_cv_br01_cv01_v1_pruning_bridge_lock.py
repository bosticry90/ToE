from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovcvbr01_cv01_v1_pruning_bridge_record import (
    ovcvbr01_cv01_v1_pruning_bridge_record,
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


def test_ov_cv_br01_lock_matches_computed_record() -> None:
    rec = ovcvbr01_cv01_v1_pruning_bridge_record(date="2026-02-08")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-CV-BR-01_cv01_v1_pruning_bridge.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked["schema"] == "OV-CV-BR-01_cv01_v1_pruning_bridge/v1"
    assert locked["observable_id"] == "OV-CV-BR-01"

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()


def test_ov_cv_br01_negative_control_lock_has_cv01_attributed_elimination() -> None:
    fixture = REPO_ROOT / "formal" / "external_evidence" / "cv01_v1_negative_control_fixture"
    rec = ovcvbr01_cv01_v1_pruning_bridge_record(
        date="2026-02-08",
        cv01_tolerance_profile="pinned",
        cv01_artifact_dir=fixture,
    )

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-CV-BR-01_cv01_v1_pruning_bridge_NEG_CONTROL.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()

    summary = dict(rec.summary)
    assert int(summary.get("cv01_attributed_elimination_count", 0)) >= 1
    assert bool(summary.get("survivor_guard")) is True
