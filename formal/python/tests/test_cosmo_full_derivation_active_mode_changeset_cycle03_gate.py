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
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "cosmo_full_discharge_active_mode_changeset_packet_cycle03_v0.json"
)
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"

PROGRESS_TOKEN = (
    "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_PROGRESS_CYCLE03_v0: "
    "ACTIVE_MODE_CHANGESET_PACKET_LOCK_PINNED"
)
CHANGESET_GATE_TOKEN = (
    "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_GATE_v0: "
    "READINESS_CHECKLIST_AND_AUTHORIZATION_GATES_REQUIRED"
)
AUTHORITY_GATE_TOKEN = (
    "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_AUTHORITY_GATE_v0: "
    "LOCKED_UNTIL_EXPLICIT_ACTIVE_MODE_CHANGESET_PACKET_AND_DISCHARGE_AUTHORITY_APPROVAL"
)
ARTIFACT_TOKEN = (
    "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_ARTIFACT_v0: "
    "cosmo_full_discharge_active_mode_changeset_packet_cycle03_v0"
)
ARTIFACT_POINTER = "formal/output/cosmo_full_discharge_active_mode_changeset_packet_cycle03_v0.json"
GATE_PATH = "formal/python/tests/test_cosmo_full_derivation_active_mode_changeset_cycle03_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_cycle03_active_mode_changeset_artifact_exists() -> None:
    assert TARGET_PATH.exists()
    assert ROADMAP_PATH.exists()
    assert STATE_PATH.exists()
    assert MATRIX_PATH.exists()
    assert ARTIFACT_PATH.exists(), "Missing cycle-03 active-mode changeset packet artifact."


def test_cosmo_cycle03_active_mode_changeset_tokens_are_cross_pinned() -> None:
    required = [
        PROGRESS_TOKEN,
        CHANGESET_GATE_TOKEN,
        AUTHORITY_GATE_TOKEN,
        ARTIFACT_TOKEN,
        ARTIFACT_POINTER,
        GATE_PATH,
    ]

    for path in [TARGET_PATH, ROADMAP_PATH, STATE_PATH]:
        text = _read(path)
        missing = [token for token in required if token not in text]
        assert not missing, f"{path} missing COSMO cycle-03 active-mode changeset token(s): " + ", ".join(missing)


def test_cosmo_cycle03_active_mode_changeset_matrix_fields_are_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO", {})

    assert (
        cosmo.get("full_discharge_active_mode_changeset_progress")
        == "ACTIVE_MODE_CHANGESET_PACKET_LOCK_PINNED"
    )
    assert (
        cosmo.get("full_discharge_active_mode_changeset_gate")
        == "READINESS_CHECKLIST_AND_AUTHORIZATION_GATES_REQUIRED"
    )
    assert (
        cosmo.get("full_discharge_active_mode_changeset_authority_gate")
        == "LOCKED_UNTIL_EXPLICIT_ACTIVE_MODE_CHANGESET_PACKET_AND_DISCHARGE_AUTHORITY_APPROVAL"
    )
    assert (
        cosmo.get("full_discharge_active_mode_changeset_artifact")
        == "formal/output/cosmo_full_discharge_active_mode_changeset_packet_cycle03_v0.json"
    )
    assert (
        cosmo.get("full_discharge_active_mode_changeset_gate_test")
        == "formal/python/tests/test_cosmo_full_derivation_active_mode_changeset_cycle03_gate.py"
    )


def test_cosmo_cycle03_active_mode_changeset_artifact_payload_is_consistent() -> None:
    payload = _read_json(ARTIFACT_PATH)

    assert payload.get("record_id") == "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_PACKET_CYCLE03_v0"
    assert payload.get("artifact_id") == "cosmo_full_discharge_active_mode_changeset_packet_cycle03_v0"
    assert payload.get("target_id") == "TARGET-COSMO-BG-PLAN"
    assert payload.get("progress_token") == PROGRESS_TOKEN

    required_bundle_tokens = {
        "COSMO_FULL_DISCHARGE_ACTIVE_TRANSITION_READINESS_PROGRESS_CYCLE02_v0: ACTIVE_DISCHARGE_IN_PROGRESS_READINESS_CHECKLIST_LOCK_PINNED",
        "COSMO_FULL_DISCHARGE_ACTIVE_TRANSITION_READINESS_GATE_v0: PREDISCHARGE_BUNDLE_AND_EXPLICIT_ACTIVE_CHANGESET_REQUIRED",
        "COSMO_FULL_DISCHARGE_ACTIVE_TRANSITION_AUTHORIZATION_GATE_v0: LOCKED_UNTIL_ACTIVE_MODE_CHANGESET_AND_DISCHARGE_AUTHORITY_APPROVAL",
        CHANGESET_GATE_TOKEN,
        AUTHORITY_GATE_TOKEN,
        "COSMO_FULL_DISCHARGE_ADJUDICATION_FLIP_BLOCK_v0: REQUIRE_EXPLICIT_DISCHARGE_GATE_CLOSURE",
        "COSMO_BACKGROUND_ADJUDICATION: NOT_YET_DISCHARGED",
        "PROCEED_GATE_COSMO: BLOCKED_v0_PHYSICS_NOT_CLOSED",
        "MATRIX_CLOSURE_GATE_COSMO: BLOCKED_v0_GOVERNANCE_NOT_CLOSED",
    }
    assert required_bundle_tokens.issubset(set(payload.get("bundle_tokens", [])))


def test_cosmo_cycle03_active_mode_changeset_does_not_flip_adjudication() -> None:
    text = _read(TARGET_PATH) + "\n" + _read(STATE_PATH) + "\n" + _read(ROADMAP_PATH)
    assert "COSMO_BACKGROUND_ADJUDICATION: NOT_YET_DISCHARGED" in text
    assert "ADJUDICATION_FLIP_GRANTED" not in text
