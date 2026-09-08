from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.toe.constraints.admissibility_manifest import GateCheckResult
from formal.python.toe.observables import (
    ovbr_snd03_cross_lane_lowk_consistency_audit_record as audit,
)
from formal.python.tools.lint_mapping_tuples import lint_mapping_tuples


REPO_ROOT = find_repo_root(Path(__file__))
MAPPING_RELATIVE_PATH = Path(
    "formal/external_evidence/bec_bragg_sound_pairing_TBD/"
    "ovbr_snd03_bragg_sound_mapping/mapping_tuples.json"
)


def _hypothesis_bytes() -> bytes:
    return (
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
        + "\n"
    ).encode("utf-8")


def test_ov_br_snd03_blocked_ignores_pairing_mapping_changes_when_gates_disabled(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """While gates are disabled, OV-BR-SND-03 must stay blocked and must not compute rows.

    This ensures mapping tuple artifacts cannot influence results under a blocked posture.
    """

    canonical_mapping_path = REPO_ROOT / MAPPING_RELATIVE_PATH
    canonical_bytes = canonical_mapping_path.read_bytes()
    temporary_repo = tmp_path / "temporary-repository"
    temporary_mapping_path = temporary_repo / MAPPING_RELATIVE_PATH
    temporary_mapping_path.parent.mkdir(parents=True)
    temporary_mapping_path.write_bytes(canonical_bytes)

    monkeypatch.setattr(audit, "find_repo_root", lambda _: temporary_repo)
    monkeypatch.setattr(
        audit,
        "check_required_gates",
        lambda **_: GateCheckResult(
            blocked=True,
            reasons=["gate_disabled:CT01", "gate_disabled:SYM01", "gate_disabled:CAUS01"],
            manifest_path="temporary-test-fixture",
            manifest_version=1,
            manifest_sha256=None,
        ),
    )

    def exercise_temporary_writer() -> tuple[bytes, dict[str, object]]:
        temporary_mapping_path.write_bytes(_hypothesis_bytes())
        written = temporary_mapping_path.read_bytes()
        rec = audit.ovbr_snd03_cross_lane_lowk_consistency_audit_record(
            status_date="2026-01-25",
            sound_date="2026-01-24",
            bragg_date="2026-01-25",
        )
        obj = rec.to_jsonable()
        temporary_mapping_path.write_bytes(canonical_bytes)
        assert temporary_mapping_path.read_bytes() == canonical_bytes
        return written, obj

    first_written, first_obj = exercise_temporary_writer()
    second_written, second_obj = exercise_temporary_writer()

    assert first_written == second_written == _hypothesis_bytes()
    for obj in (first_obj, second_obj):
        assert obj["status"]["blocked"] is True
        assert obj["comparability"]["status"] == "blocked"
        assert "GATES_DISABLED" in obj["comparability"]["reasons"]
        assert obj["rows"] == []
        assert obj["comparability"]["status"] not in {"absent", "hypothesis_only", "established"}
    assert canonical_mapping_path.read_bytes() == canonical_bytes


def test_mapping_tuple_repository_validation_is_read_only() -> None:
    mapping_path = REPO_ROOT / MAPPING_RELATIVE_PATH
    before = mapping_path.read_bytes()
    result = lint_mapping_tuples()
    assert result.errors == []
    assert mapping_path.read_bytes() == before
