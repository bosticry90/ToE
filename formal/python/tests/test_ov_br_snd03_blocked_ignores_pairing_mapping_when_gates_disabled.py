from __future__ import annotations

import json
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


def test_ov_br_snd03_blocked_ignores_pairing_mapping_changes_when_gates_disabled() -> None:
    """While gates are disabled, OV-BR-SND-03 must stay blocked and must not compute rows.

    This ensures mapping tuple artifacts cannot influence results under a blocked posture.
    """

    mapping_path = (
        REPO_ROOT
        / "formal"
        / "external_evidence"
        / "bec_bragg_sound_pairing_TBD"
        / "ovbr_snd03_bragg_sound_mapping"
        / "mapping_tuples.json"
    )

    original = mapping_path.read_text(encoding="utf-8")
    try:
        # Write a schema-valid, non-empty mapping (hypothesis tuple).
        mapping_path.write_text(
            json.dumps(
                {
                    "schema": "OV-BR-SND-03_explicit_bragg_sound_pairing_tuples/v4",
                    "mapping_tuples": [
                        {
                            "tuple_id": "hypothesis_example_only",
                            "bragg_key": "br04a_conditionA",
                            "sound_key": "snd02_single",
                            "pair_type": "cross_source_hypothesis",
                            "rationale": "Test-only tuple; should not be consulted while gates are disabled.",
                            "source_locators": {},
                        }
                    ],
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )

        rec = ovbr_snd03_cross_lane_lowk_consistency_audit_record(
            status_date="2026-01-25",
            sound_date="2026-01-24",
            bragg_date="2026-01-25",
        )
        obj = rec.to_jsonable()

        assert obj["status"]["blocked"] is True
        assert obj["comparability"]["status"] == "blocked"
        assert "GATES_DISABLED" in obj["comparability"]["reasons"]
        assert obj["rows"] == []

        # No non-blocked statuses are emitted while blocked.
        assert obj["comparability"]["status"] not in {"absent", "hypothesis_only", "established"}
    finally:
        mapping_path.write_text(original, encoding="utf-8")
