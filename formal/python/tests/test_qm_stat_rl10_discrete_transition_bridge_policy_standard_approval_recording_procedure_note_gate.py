from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    path = start.resolve()
    while path != path.parent:
        if (path / "formal").exists() and (path / "README.md").exists():
            return path
        path = path.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
NOTE_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_v0.md"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
STOP_STATE_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "RESTART_GOVERNANCE_STOP_STATE_SUMMARY_20260414_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qm_stat_rl10_policy_standard_approval_recording_procedure_note_gate() -> None:
    note_text = _read(NOTE_PATH)
    state_text = _read(STATE_PATH)
    stop_state_text = _read(STOP_STATE_PATH)

    for token in (
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_REQUIRED_FIELDS_v0: APPROVAL_DECISION_ID_PLUS_APPROVAL_DECISION_TIMESTAMP_UTC_PLUS_APPROVAL_AUTHORITY_ID_PLUS_APPROVAL_ATTESTATION_REFERENCE",
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_NON_EQUIVALENCE_RULE_v0: RECORDING_APPROVAL_DOES_NOT_ITSELF_AUTHORIZE_RESTART_OR_OPEN_QM_STAT_EXECUTION",
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_STATUS_v0: PROCEDURE_DEFINED_BUT_NOT_EXECUTED",
    ):
        assert token in note_text

    for field_name in (
        "`approval_decision_id`",
        "`approval_decision_timestamp_utc`",
        "`approval_authority_id`",
        "`approval_attestation_reference`",
    ):
        assert field_name in note_text

    for required_ref in (
        "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_v0.md",
        "formal/docs/release/RESTART_GOVERNANCE_STOP_STATE_SUMMARY_20260414_v0.md",
        "formal/output/reports/qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
    ):
        assert required_ref in note_text

    for boundary in (
        "Do not write placeholder approval fields or speculative attestations.",
        "Do not treat this procedure as sufficient to authorize restart.",
        "Do not open QM-STAT execution before downstream rerun confirms the blocker moved.",
    ):
        assert boundary in note_text

    assert "policy_standard_approval_not_recorded" in note_text
    assert "policy_standard_approval_not_recorded" in stop_state_text
    assert (
        "Canonical stop-state layer: P93 approval-recording procedure declared, unexecuted, "
        "and fail-closed pending a real approval record"
    ) in stop_state_text
    assert "- approval-recording procedure definition" in stop_state_text
    assert "- approval-recording procedure exists and is unexecuted" in stop_state_text
    assert (
        "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_NEXT_ACTION_v0: "
        "WAIT_FOR_REAL_APPROVAL_THEN_RECORD_ON_DECLARED_SURFACE_AND_RERUN_RESTART_CHAIN"
    ) in state_text