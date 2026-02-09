from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovbr02_regime_bridge_record import ovbr02_regime_bridge_record


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


def test_ov_br02_dq01_v2_lock_matches_computed_record_and_has_no_failure_reasons() -> None:
    rec = ovbr02_regime_bridge_record(adequacy_policy="DQ-01_v2", q_threshold=1.05)

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-02_regime_bridge_record_DQ-01_v2.md"
    )
    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(text) == rec.fingerprint()

    lp = locked.get("low_preference") or {}
    hp = locked.get("high_preference") or {}

    assert (lp.get("failure_reasons") or []) == []
    assert (hp.get("failure_reasons") or []) == []

    assert bool(lp.get("prefer_curved")) is True
    assert bool(hp.get("prefer_curved")) is True
    assert bool(lp.get("robustness_failed")) is False
    assert bool(hp.get("robustness_failed")) is False

    # Under DQ-01_v2 threshold-only variant, OV-03x is no longer q_ratio-blocked.
    assert "q_ratio_above_threshold" not in (hp.get("failure_reasons") or [])
