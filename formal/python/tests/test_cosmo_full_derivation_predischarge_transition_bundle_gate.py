from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_full_discharge_predischarge_transition_bundle_cycle01_v0.json"

PROGRESS_TOKEN = (
    "COSMO_FULL_DISCHARGE_PREDISCHARGE_TRANSITION_PROGRESS_CYCLE01_v0: "
    "PREDISCHARGE_TRANSITION_BUNDLE_LOCK_PINNED"
)
GATE_TOKEN = (
    "COSMO_FULL_DISCHARGE_PREDISCHARGE_TRANSITION_BUNDLE_GATE_v0: "
    "EXIT_ROW_CRITERIA_AND_AUTHORIZATION_PACKET_AND_REGISTRY_CHAIN_REQUIRED"
)
FLIP_BLOCK_TOKEN = "COSMO_FULL_DISCHARGE_ADJUDICATION_FLIP_BLOCK_v0: REQUIRE_EXPLICIT_DISCHARGE_GATE_CLOSURE"
ARTIFACT_TOKEN = (
    "COSMO_FULL_DISCHARGE_PREDISCHARGE_TRANSITION_BUNDLE_ARTIFACT_v0: "
    "cosmo_full_discharge_predischarge_transition_bundle_cycle01_v0"
)
ARTIFACT_POINTER = "formal/output/cosmo_full_discharge_predischarge_transition_bundle_cycle01_v0.json"
GATE_PATH = "formal/python/tests/test_cosmo_full_derivation_predischarge_transition_bundle_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_predischarge_transition_artifact_exists() -> None:
    assert TARGET_PATH.exists()
    assert ROADMAP_PATH.exists()
    assert STATE_PATH.exists()
    assert MATRIX_PATH.exists()
    assert ARTIFACT_PATH.exists(), "Missing COSMO pre-discharge transition bundle artifact."


def test_cosmo_predischarge_transition_tokens_are_cross_pinned() -> None:
    required = [
        PROGRESS_TOKEN,
        GATE_TOKEN,
        FLIP_BLOCK_TOKEN,
        ARTIFACT_TOKEN,
        ARTIFACT_POINTER,
        GATE_PATH,
    ]

    for path in [TARGET_PATH, ROADMAP_PATH, STATE_PATH]:
        text = _read(path)
        missing = [token for token in required if token not in text]
        assert not missing, f"{path} missing COSMO pre-discharge transition token(s): " + ", ".join(missing)


def test_cosmo_predischarge_transition_matrix_fields_are_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO", {})

    assert cosmo.get("full_discharge_predischarge_transition_progress") == "PREDISCHARGE_TRANSITION_BUNDLE_LOCK_PINNED"
    assert (
        cosmo.get("full_discharge_predischarge_transition_bundle_gate")
        == "EXIT_ROW_CRITERIA_AND_AUTHORIZATION_PACKET_AND_REGISTRY_CHAIN_REQUIRED"
    )
    assert cosmo.get("full_discharge_adjudication_flip_block") == "REQUIRE_EXPLICIT_DISCHARGE_GATE_CLOSURE"
    assert (
        cosmo.get("full_discharge_predischarge_transition_bundle_artifact")
        == "formal/output/cosmo_full_discharge_predischarge_transition_bundle_cycle01_v0.json"
    )
    assert (
        cosmo.get("full_discharge_predischarge_transition_bundle_gate_test")
        == "formal/python/tests/test_cosmo_full_derivation_predischarge_transition_bundle_gate.py"
    )


def test_cosmo_predischarge_transition_artifact_payload_is_consistent() -> None:
    payload = _read_json(ARTIFACT_PATH)

    assert payload.get("record_id") == "COSMO_FULL_DISCHARGE_PREDISCHARGE_TRANSITION_BUNDLE_CYCLE01_v0"
    assert payload.get("artifact_id") == "cosmo_full_discharge_predischarge_transition_bundle_cycle01_v0"
    assert payload.get("target_id") == "TARGET-COSMO-BG-PLAN"
    assert payload.get("progress_token") == PROGRESS_TOKEN

    required_bundle_tokens = {
        GATE_TOKEN,
        FLIP_BLOCK_TOKEN,
        "COSMO_FULL_DISCHARGE_EXIT_ROW_READINESS_GATE_v0: LOCKED_UNTIL_CHECKLIST_ARTIFACT_AND_ROW_STATUS_NON_BLOCKED",
        "COSMO_FULL_DISCHARGE_EXIT_ROW_AUTHORIZATION_PACKET_GATE_v0: LOCKED_UNTIL_EXPLICIT_AUTHORIZATION_PACKET_PRESENT_AND_ROADMAP_GATES_CLOSED",
        "COSMO_BACKGROUND_ADJUDICATION: NOT_YET_DISCHARGED",
        "PROCEED_GATE_COSMO: BLOCKED_v0_PHYSICS_NOT_CLOSED",
        "MATRIX_CLOSURE_GATE_COSMO: BLOCKED_v0_GOVERNANCE_NOT_CLOSED",
    }
    assert required_bundle_tokens.issubset(set(payload.get("bundle_tokens", [])))


def test_cosmo_predischarge_transition_does_not_flip_adjudication() -> None:
    text = _read(TARGET_PATH) + "\n" + _read(STATE_PATH) + "\n" + _read(ROADMAP_PATH)
    assert "COSMO_BACKGROUND_ADJUDICATION: NOT_YET_DISCHARGED" in text
    assert "ADJUDICATION_FLIP_GRANTED" not in text
