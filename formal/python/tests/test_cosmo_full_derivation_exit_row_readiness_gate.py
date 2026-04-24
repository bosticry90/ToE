from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_full_discharge_exit_row_readiness_cycle01_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_exit_row_readiness_tokens_are_cross_pinned() -> None:
    required_tokens = [
        "COSMO_FULL_DISCHARGE_EXIT_ROW_01_NON_BLOCK_CONDITIONS_v0: CYCLE91_CANONICAL_ARTIFACT_AND_COMPLETION_CRITERIA_ARTIFACT_REQUIRED",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_02_NON_BLOCK_CONDITIONS_v0: ROADMAP_GATES_CLOSED_AND_EXPLICIT_AUTHORIZATION_PACKET_REQUIRED",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_STATUS_v0: AUTHORIZATION_PENDING",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_GATE_v0: LOCKED_UNTIL_EXPLICIT_AUTHORIZATION_PACKET_PRESENT_AND_ROADMAP_GATES_CLOSED",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_ARTIFACT_v0: cosmo_full_discharge_exit_row_authorization_packet_cycle01_v0",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_READINESS_ARTIFACT_v0: cosmo_full_discharge_exit_row_readiness_cycle01_v0",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_READINESS_GATE_v0: LOCKED_UNTIL_CHECKLIST_ARTIFACT_AND_ROW_STATUS_NON_BLOCKED",
        "formal/output/cosmo_full_discharge_exit_row_authorization_packet_cycle01_v0.json",
        "formal/python/tests/test_cosmo_full_derivation_exit_row_authorization_packet_gate.py",
        "formal/output/cosmo_full_discharge_exit_row_readiness_cycle01_v0.json",
        "formal/python/tests/test_cosmo_full_derivation_exit_row_readiness_gate.py",
    ]

    for path in [TARGET_PATH, STATE_PATH, ROADMAP_PATH, RESULTS_PATH]:
        text = _read(path)
        missing = [token for token in required_tokens if token not in text]
        assert not missing, f"{path} missing COSMO readiness token(s): " + ", ".join(missing)


def test_cosmo_exit_row_readiness_artifact_payload_is_consistent() -> None:
    payload = _read_json(ARTIFACT_PATH)
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO", {})

    assert payload.get("record_id") == "COSMO_FULL_DISCHARGE_EXIT_ROW_READINESS_CYCLE01_v0"
    assert payload.get("artifact_id") == "cosmo_full_discharge_exit_row_readiness_cycle01_v0"
    assert payload.get("scope") == "cosmo_full_discharge_exit_row_readiness_v0"
    assert payload.get("readiness_gate_token") == "COSMO_FULL_DISCHARGE_EXIT_ROW_READINESS_GATE_v0"
    assert payload.get("readiness_gate_value") == "LOCKED_UNTIL_CHECKLIST_ARTIFACT_AND_ROW_STATUS_NON_BLOCKED"
    assert payload.get("required_results_rows") == ["TOE-COSMO-DER-01", "TOE-COSMO-DER-02"]
    assert payload.get("current_row_statuses") == {
        "TOE-COSMO-DER-01": "B-BLOCKED",
        "TOE-COSMO-DER-02": "B-BLOCKED",
    }
    assert payload.get("current_roadmap_gate_tokens") == {
        "PROCEED_GATE_COSMO": "BLOCKED_v0_PHYSICS_NOT_CLOSED",
        "MATRIX_CLOSURE_GATE_COSMO": "BLOCKED_v0_GOVERNANCE_NOT_CLOSED",
    }

    assert cosmo.get("full_discharge_exit_row_01_non_block_conditions") == (
        "CYCLE91_CANONICAL_ARTIFACT_AND_COMPLETION_CRITERIA_ARTIFACT_REQUIRED"
    )
    assert cosmo.get("full_discharge_exit_row_02_non_block_conditions") == (
        "ROADMAP_GATES_CLOSED_AND_EXPLICIT_AUTHORIZATION_PACKET_REQUIRED"
    )
    assert cosmo.get("full_discharge_exit_row_readiness_artifact") == (
        "formal/output/cosmo_full_discharge_exit_row_readiness_cycle01_v0.json"
    )
    assert cosmo.get("full_discharge_exit_row_readiness_gate") == (
        "LOCKED_UNTIL_CHECKLIST_ARTIFACT_AND_ROW_STATUS_NON_BLOCKED"
    )
    assert cosmo.get("full_discharge_exit_row_readiness_gate_test") == (
        "formal/python/tests/test_cosmo_full_derivation_exit_row_readiness_gate.py"
    )
    assert cosmo.get("full_discharge_exit_row_authorization_packet_status") == "AUTHORIZATION_PENDING"
    assert (
        cosmo.get("full_discharge_exit_row_authorization_packet_gate")
        == "LOCKED_UNTIL_EXPLICIT_AUTHORIZATION_PACKET_PRESENT_AND_ROADMAP_GATES_CLOSED"
    )
    assert (
        cosmo.get("full_discharge_exit_row_authorization_packet_artifact")
        == "formal/output/cosmo_full_discharge_exit_row_authorization_packet_cycle01_v0.json"
    )
    assert (
        cosmo.get("full_discharge_exit_row_authorization_packet_gate_test")
        == "formal/python/tests/test_cosmo_full_derivation_exit_row_authorization_packet_gate.py"
    )


def test_cosmo_exit_row_readiness_stays_locked_and_no_flip_token() -> None:
    payload = _read_json(ARTIFACT_PATH)
    decision = payload.get("readiness_decision")
    assert isinstance(decision, dict)
    assert decision.get("exit_rows_can_move_to_non_blocked_now") is False
    assert decision.get("reason") == "rows_and_roadmap_gates_remain_blocked"
    assert payload.get("authorization_packet") == {
        "status_token": "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_STATUS_v0",
        "status_value": "AUTHORIZATION_PENDING",
        "gate_token": "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_GATE_v0",
        "gate_value": "LOCKED_UNTIL_EXPLICIT_AUTHORIZATION_PACKET_PRESENT_AND_ROADMAP_GATES_CLOSED",
    }

    combined = _read(TARGET_PATH) + "\n" + _read(STATE_PATH) + "\n" + _read(ROADMAP_PATH)
    assert "ADJUDICATION_FLIP_GRANTED" not in combined
