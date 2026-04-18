from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
COSMO_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "cosmo_background_full_discharge_adjudication_criteria_cycle01_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_adjudication_criteria_pointers_are_cross_pinned() -> None:
    required_tokens = [
        "COSMO_BACKGROUND_FULL_DISCHARGE_CRITERIA_ROW_01_v0: MICRO_CYCLE_COHERENCE_AND_CANONICAL_ARTIFACT_PINNED",
        "COSMO_BACKGROUND_FULL_DISCHARGE_CRITERIA_ROW_02_v0: COMPLETION_AUTHORITY_AND_FLIP_GATING_PINNED",
        "COSMO_BACKGROUND_FULL_DISCHARGE_EXIT_ROW_01_STATUS_v0: TOE-COSMO-DER-01_B-BLOCKED_PENDING_DISCHARGE",
        "COSMO_BACKGROUND_FULL_DISCHARGE_EXIT_ROW_02_STATUS_v0: TOE-COSMO-DER-02_B-BLOCKED_PENDING_DISCHARGE",
        (
            "COSMO_BACKGROUND_FULL_DISCHARGE_ADJUDICATION_CRITERIA_ARTIFACT_v0: "
            "cosmo_background_full_discharge_adjudication_criteria_cycle01_v0"
        ),
        (
            "COSMO_BACKGROUND_FULL_DISCHARGE_ADJUDICATION_FLIP_GATE_v0: "
            "CRITERIA_ARTIFACT_AND_COMPLETION_ROWS_REQUIRED_NO_STATUS_FLIP_WITHOUT_AUTHORIZATION"
        ),
        "REQUIRED_COSMO_CLOSURE_ROWS: TOE-COSMO-DER-01,TOE-COSMO-DER-02",
        "PROCEED_GATE_COSMO: BLOCKED_v0_PHYSICS_NOT_CLOSED",
        "MATRIX_CLOSURE_GATE_COSMO: BLOCKED_v0_GOVERNANCE_NOT_CLOSED",
        "formal/output/cosmo_background_full_discharge_adjudication_criteria_cycle01_v0.json",
        "formal/python/tests/test_cosmo_background_full_discharge_adjudication_criteria_artifact.py",
        "formal/python/tests/test_cosmo_full_derivation_discharge_lane_gate.py",
    ]

    for path in [COSMO_TARGET_PATH, STATE_PATH]:
        text = _read(path)
        missing = [token for token in required_tokens if token not in text]
        assert not missing, f"{path} missing COSMO completion-lane token(s): " + ", ".join(missing)

    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO", {})
    assert (
        cosmo.get("full_discharge_adjudication_criteria_artifact")
        == "formal/output/cosmo_background_full_discharge_adjudication_criteria_cycle01_v0.json"
    )
    assert (
        cosmo.get("full_discharge_adjudication_criteria_gate")
        == "formal/python/tests/test_cosmo_background_full_discharge_adjudication_criteria_artifact.py"
    )
    assert (
        cosmo.get("full_discharge_adjudication_flip_gate")
        == "CRITERIA_ARTIFACT_AND_COMPLETION_ROWS_REQUIRED_NO_STATUS_FLIP_WITHOUT_AUTHORIZATION"
    )
    assert cosmo.get("full_discharge_exit_row_01_status") == "TOE-COSMO-DER-01_B-BLOCKED_PENDING_DISCHARGE"
    assert cosmo.get("full_discharge_exit_row_02_status") == "TOE-COSMO-DER-02_B-BLOCKED_PENDING_DISCHARGE"
    assert cosmo.get("required_cosmo_closure_rows") == "TOE-COSMO-DER-01,TOE-COSMO-DER-02"
    assert cosmo.get("proceed_gate_cosmo") == "BLOCKED_v0_PHYSICS_NOT_CLOSED"
    assert cosmo.get("matrix_closure_gate_cosmo") == "BLOCKED_v0_GOVERNANCE_NOT_CLOSED"
    assert cosmo.get("full_discharge_lane_gate") == "formal/python/tests/test_cosmo_full_derivation_discharge_lane_gate.py"


def test_cosmo_adjudication_criteria_artifact_payload_is_well_formed() -> None:
    payload = _read_json(ARTIFACT_PATH)

    assert payload.get("record_id") == "COSMO_BACKGROUND_FULL_DISCHARGE_ADJUDICATION_CRITERIA_CYCLE01_v0"
    assert payload.get("artifact_id") == "cosmo_background_full_discharge_adjudication_criteria_cycle01_v0"
    assert payload.get("scope") == "cosmo_background_full_discharge_adjudication_criteria_v0"
    assert payload.get("pillar") == "PILLAR-COSMO"
    assert payload.get("adjudication_token") == "COSMO_BACKGROUND_ADJUDICATION"
    assert payload.get("adjudication_posture") == "NOT_YET_DISCHARGED"

    criteria_rows = payload.get("criteria_rows")
    assert isinstance(criteria_rows, list) and len(criteria_rows) == 2
    assert [row.get("row_id") for row in criteria_rows] == [
        "COSMO_BACKGROUND_FULL_DISCHARGE_CRITERIA_ROW_01_v0",
        "COSMO_BACKGROUND_FULL_DISCHARGE_CRITERIA_ROW_02_v0",
    ]
    assert all(row.get("status") == "PINNED" for row in criteria_rows)
    assert payload.get("required_results_rows") == ["TOE-COSMO-DER-01", "TOE-COSMO-DER-02"]
    assert payload.get("current_row_statuses") == {
        "TOE-COSMO-DER-01": "B-BLOCKED",
        "TOE-COSMO-DER-02": "B-BLOCKED",
    }
    assert payload.get("current_roadmap_gate_tokens") == {
        "PILLAR-COSMO_PHYSICS_STATUS": "OPEN_v0_LOCKED_QUEUE_PENDING_DISCHARGE_ROWS",
        "PILLAR-COSMO_GOVERNANCE_STATUS": "OPEN_v0_REQUIRED_ROWS_BLOCKED",
        "PROCEED_GATE_COSMO": "BLOCKED_v0_PHYSICS_NOT_CLOSED",
        "MATRIX_CLOSURE_GATE_COSMO": "BLOCKED_v0_GOVERNANCE_NOT_CLOSED",
    }
    assert payload.get("required_artifacts") == [
        "formal/output/cosmo_bg_micro91_dryrun_nonflip_boundary_execution_custody_recertification_continuity_audit_cycle01_v0.json",
        "formal/output/cosmo_full_discharge_exit_row_readiness_cycle01_v0.json",
    ]


def test_cosmo_adjudication_criteria_artifact_encodes_no_premature_flip() -> None:
    payload = _read_json(ARTIFACT_PATH)

    flip_preconditions = payload.get("flip_preconditions")
    assert isinstance(flip_preconditions, dict)
    assert flip_preconditions.get("adjudication_must_start_with") == "DISCHARGED_"
    assert flip_preconditions.get("all_criteria_rows_must_be_pinned") is True
    assert flip_preconditions.get("explicit_authorization_required") is True
    assert flip_preconditions.get("forbid_premature_flip_token") == "ADJUDICATION_FLIP_GRANTED"

    flip_readiness = payload.get("flip_readiness")
    assert isinstance(flip_readiness, dict)
    assert flip_readiness.get("adjudication_flip_allowed_now") is False
    assert flip_readiness.get("reason") == "adjudication_not_discharged_completion_lane_only"

    combined_narrative = _read(COSMO_TARGET_PATH) + "\n" + _read(STATE_PATH)
    assert "ADJUDICATION_FLIP_GRANTED" not in combined_narrative
