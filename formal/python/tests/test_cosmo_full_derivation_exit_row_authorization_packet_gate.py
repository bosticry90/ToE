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
TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
PACKET_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_v0.md"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_full_discharge_exit_row_authorization_packet_cycle01_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_authorization_packet_tokens_are_cross_pinned() -> None:
    required_tokens = [
        "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_STATUS_v0: AUTHORIZATION_PENDING",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_GATE_v0: LOCKED_UNTIL_EXPLICIT_AUTHORIZATION_PACKET_PRESENT_AND_ROADMAP_GATES_CLOSED",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_ARTIFACT_v0: cosmo_full_discharge_exit_row_authorization_packet_cycle01_v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_v0.md",
        "formal/output/cosmo_full_discharge_exit_row_authorization_packet_cycle01_v0.json",
        "formal/python/tests/test_cosmo_full_derivation_exit_row_authorization_packet_gate.py",
    ]

    for path in [TARGET_PATH, PACKET_DOC_PATH, STATE_PATH, ROADMAP_PATH, RESULTS_PATH]:
        text = _read(path)
        missing = [token for token in required_tokens if token not in text]
        assert not missing, f"{path} missing COSMO authorization-packet token(s): " + ", ".join(missing)


def test_cosmo_authorization_packet_artifact_payload_and_matrix_are_consistent() -> None:
    payload = _read_json(ARTIFACT_PATH)
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO", {})

    assert payload.get("record_id") == "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_CYCLE01_v0"
    assert payload.get("artifact_id") == "cosmo_full_discharge_exit_row_authorization_packet_cycle01_v0"
    assert payload.get("scope") == "cosmo_full_discharge_exit_row_authorization_packet_v0"

    assert payload.get("packet_status") == {
        "token": "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_STATUS_v0",
        "value": "AUTHORIZATION_PENDING",
    }
    assert payload.get("packet_gate") == {
        "token": "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_GATE_v0",
        "value": "LOCKED_UNTIL_EXPLICIT_AUTHORIZATION_PACKET_PRESENT_AND_ROADMAP_GATES_CLOSED",
    }
    assert payload.get("current_roadmap_gate_tokens") == {
        "PROCEED_GATE_COSMO": "BLOCKED_v0_PHYSICS_NOT_CLOSED",
        "MATRIX_CLOSURE_GATE_COSMO": "BLOCKED_v0_GOVERNANCE_NOT_CLOSED",
    }

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
        cosmo.get("full_discharge_exit_row_authorization_packet_doc")
        == "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_v0.md"
    )
    assert (
        cosmo.get("full_discharge_exit_row_authorization_packet_gate_test")
        == "formal/python/tests/test_cosmo_full_derivation_exit_row_authorization_packet_gate.py"
    )


def test_cosmo_authorization_packet_stays_pending_no_flip_tokens() -> None:
    payload = _read_json(ARTIFACT_PATH)
    decision = payload.get("authorization_decision")
    assert isinstance(decision, dict)
    assert decision.get("packet_satisfies_row02_non_block_requirement_now") is False
    assert decision.get("reason") == "roadmap_gates_not_closed"

    combined = _read(TARGET_PATH) + "\n" + _read(PACKET_DOC_PATH) + "\n" + _read(STATE_PATH)
    assert "ADJUDICATION_FLIP_GRANTED" not in combined
    assert "COMPARATOR_LANE_AUTHORIZATION_GRANTED" not in combined
