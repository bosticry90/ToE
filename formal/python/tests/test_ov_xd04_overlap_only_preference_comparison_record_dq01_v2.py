from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovxd04_overlap_only_preference_comparison_record import (
    ovxd04_overlap_only_preference_comparison_record,
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


def test_ov_xd04_dq01_v2_lock_matches_computed_record_and_is_both_decsive_agreement_true() -> None:
    rec = ovxd04_overlap_only_preference_comparison_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md"
    )
    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(text) == rec.fingerprint()

    assert locked["schema"] == "OV-XD-04/v1"
    assert locked["decisiveness"] == "both-decisive"
    assert bool(locked["agreement"]) is True
    assert locked["low_preferred_family"] == "curved"
    assert locked["high_preferred_family"] == "curved"
