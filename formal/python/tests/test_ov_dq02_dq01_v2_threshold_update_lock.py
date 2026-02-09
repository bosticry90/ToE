from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovdq02_dq01_v2_threshold_update_record import (
    ovdq02_dq01_v2_threshold_update_record,
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


def test_ov_dq02_policy_lock_matches_computed() -> None:
    lock_path = REPO_ROOT / "formal" / "markdown" / "locks" / "policies" / "DQ-01_v2_threshold_update.md"
    assert lock_path.exists(), f"Missing lock: {lock_path.as_posix()}"

    rec = ovdq02_dq01_v2_threshold_update_record().to_jsonable()

    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    assert locked == rec
    assert _extract_record_fingerprint(text) == ovdq02_dq01_v2_threshold_update_record().fingerprint()


def test_ov_dq02_delta_is_threshold_only_and_impact_is_ov03x_only() -> None:
    rec = ovdq02_dq01_v2_threshold_update_record().to_jsonable()

    assert rec["from_policy"] == "DQ-01_v1"
    assert rec["to_policy"] == "DQ-01_v2"
    assert abs(float(rec["q_threshold_from"]) - 0.90) <= 1e-12
    assert abs(float(rec["q_threshold_to"]) - 1.05) <= 1e-12

    delta = dict(rec["delta"])
    assert list(delta.get("changed_fields")) == ["q_threshold"]

    assert list(rec["impact_set"]) == ["OV-03x"]
