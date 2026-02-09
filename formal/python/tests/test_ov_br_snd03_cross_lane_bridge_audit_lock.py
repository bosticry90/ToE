from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovbr_snd03_cross_lane_lowk_consistency_audit_record import (
    ovbr_snd03_cross_lane_lowk_consistency_audit_record,
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


def test_ov_br_snd03_lock_matches_computed_and_is_conservative_when_no_mapping() -> None:
    rec = ovbr_snd03_cross_lane_lowk_consistency_audit_record(
        status_date="2026-01-25",
        sound_date="2026-01-24",
        bragg_date="2026-01-25",
    )

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-SND-03_cross_lane_lowk_consistency_audit.md"
    )

    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()

    # If admissibility gates are disabled (default posture), the record is blocked and does not
    # compute rows/metrics.
    if bool(locked["status"].get("blocked", False)):
        assert locked["comparability"]["status"] == "blocked"
        assert "GATES_DISABLED" in locked["comparability"]["reasons"]
        assert locked["rows"] == []
        assert "admissibility_manifest_blocked" in locked["status"].get("blockers", [])
        return

    assert locked["status"]["blocked"] is False
    assert locked["comparability"]["status"] in {"absent", "hypothesis_only", "established"}

    # v3 adds explicit conversion + criterion sections.
    assert "conversion_chain" in locked["comparability"]
    assert "criterion" in locked["comparability"]
    assert locked["comparability"]["conversion_chain"]["rule_id"] == "unit_chain_v1"
    assert locked["comparability"]["criterion"]["criterion_id"] == "lowk_velocity_ratio_v1"

    mapping = locked["status"]["inputs"]["mapping_tuples"]["ovbr_snd03_bragg_sound_pairing"]
    if not bool(mapping.get("bragg_sound_mapping_present")):
        assert locked["comparability"]["status"] == "absent"
        for rc in [
            "NO_MAPPING_TUPLE",
            "NO_JUSTIFIED_PAIRING",
            "CONVERSION_CHAIN_PINNED",
            "CRITERION_DEFINED",
        ]:
            assert rc in locked["comparability"]["reasons"]

        for row in locked["rows"]:
            assert row["comparability"]["status"] == "not_compared"
            assert row.get("pair_type") == "none"
            for rc in [
                "NO_MAPPING_TUPLE",
                "NO_JUSTIFIED_PAIRING",
                "CONVERSION_CHAIN_PINNED",
                "CRITERION_DEFINED",
            ]:
                assert rc in row["comparability"]["reason_codes"]
