from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "cosmo_full_discharge_active_mode_changeset_endorsement_packet_cycle12_v0.json"
)
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"

PROGRESS_TOKEN = (
    "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_ENDORSEMENT_PROGRESS_CYCLE12_v0: "
    "ACTIVE_MODE_CHANGESET_ENDORSEMENT_PACKET_LOCK_PINNED"
)
ENDORSEMENT_GATE_TOKEN = (
    "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_ENDORSEMENT_GATE_v0: "
    "CYCLE11_AFFIRMATION_PACKET_AND_AUTHORITY_GATE_REQUIRED"
)
ENDORSEMENT_AUTHORITY_GATE_TOKEN = (
    "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_ENDORSEMENT_AUTHORITY_GATE_v0: "
    "LOCKED_UNTIL_ACTIVE_MODE_CHANGESET_ENDORSEMENT_PACKET_AND_DISCHARGE_AUTHORITY_APPROVAL"
)
ARTIFACT_TOKEN = (
    "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_ENDORSEMENT_ARTIFACT_v0: "
    "cosmo_full_discharge_active_mode_changeset_endorsement_packet_cycle12_v0"
)
ARTIFACT_POINTER = "formal/output/cosmo_full_discharge_active_mode_changeset_endorsement_packet_cycle12_v0.json"
GATE_PATH = "formal/python/tests/test_cosmo_full_derivation_active_mode_changeset_endorsement_cycle12_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_cycle12_active_mode_changeset_endorsement_artifact_exists() -> None:
    assert TARGET_PATH.exists()
    assert ROADMAP_PATH.exists()
    assert STATE_PATH.exists()
    assert MATRIX_PATH.exists()
    assert ARTIFACT_PATH.exists(), "Missing cycle-12 active-mode changeset endorsement artifact."


def test_cosmo_cycle12_active_mode_changeset_endorsement_tokens_are_cross_pinned() -> None:
    required = [
        PROGRESS_TOKEN,
        ENDORSEMENT_GATE_TOKEN,
        ENDORSEMENT_AUTHORITY_GATE_TOKEN,
        ARTIFACT_TOKEN,
        ARTIFACT_POINTER,
        GATE_PATH,
    ]

    for path in [TARGET_PATH, ROADMAP_PATH, STATE_PATH]:
        text = _read(path)
        missing = [token for token in required if token not in text]
        assert not missing, f"{path} missing COSMO cycle-12 active-mode changeset endorsement token(s): " + ", ".join(
            missing
        )


def test_cosmo_cycle12_active_mode_changeset_endorsement_matrix_fields_are_pinned() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO", {})

    assert (
        cosmo.get("full_discharge_active_mode_changeset_endorsement_progress")
        == "ACTIVE_MODE_CHANGESET_ENDORSEMENT_PACKET_LOCK_PINNED"
    )
    assert (
        cosmo.get("full_discharge_active_mode_changeset_endorsement_gate")
        == "CYCLE11_AFFIRMATION_PACKET_AND_AUTHORITY_GATE_REQUIRED"
    )
    assert (
        cosmo.get("full_discharge_active_mode_changeset_endorsement_authority_gate")
        == "LOCKED_UNTIL_ACTIVE_MODE_CHANGESET_ENDORSEMENT_PACKET_AND_DISCHARGE_AUTHORITY_APPROVAL"
    )
    assert (
        cosmo.get("full_discharge_active_mode_changeset_endorsement_artifact")
        == "formal/output/cosmo_full_discharge_active_mode_changeset_endorsement_packet_cycle12_v0.json"
    )
    assert (
        cosmo.get("full_discharge_active_mode_changeset_endorsement_gate_test")
        == "formal/python/tests/test_cosmo_full_derivation_active_mode_changeset_endorsement_cycle12_gate.py"
    )


def test_cosmo_cycle12_active_mode_changeset_endorsement_artifact_payload_is_consistent() -> None:
    payload = _read_json(ARTIFACT_PATH)

    assert payload.get("record_id") == "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_ENDORSEMENT_PACKET_CYCLE12_v0"
    assert payload.get("artifact_id") == "cosmo_full_discharge_active_mode_changeset_endorsement_packet_cycle12_v0"
    assert payload.get("target_id") == "TARGET-COSMO-BG-PLAN"
    assert payload.get("progress_token") == PROGRESS_TOKEN

    required_bundle_tokens = {
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_AFFIRMATION_PROGRESS_CYCLE11_v0: ACTIVE_MODE_CHANGESET_AFFIRMATION_PACKET_LOCK_PINNED",
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_AFFIRMATION_GATE_v0: CYCLE10_ACKNOWLEDGMENT_PACKET_AND_AUTHORITY_GATE_REQUIRED",
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_AFFIRMATION_AUTHORITY_GATE_v0: LOCKED_UNTIL_ACTIVE_MODE_CHANGESET_AFFIRMATION_PACKET_AND_DISCHARGE_AUTHORITY_APPROVAL",
        ENDORSEMENT_GATE_TOKEN,
        ENDORSEMENT_AUTHORITY_GATE_TOKEN,
        "COSMO_FULL_DISCHARGE_ADJUDICATION_FLIP_BLOCK_v0: REQUIRE_EXPLICIT_DISCHARGE_GATE_CLOSURE",
        "COSMO_BACKGROUND_ADJUDICATION: NOT_YET_DISCHARGED",
        "PROCEED_GATE_COSMO: BLOCKED_v0_PHYSICS_NOT_CLOSED",
        "MATRIX_CLOSURE_GATE_COSMO: BLOCKED_v0_GOVERNANCE_NOT_CLOSED",
    }
    assert required_bundle_tokens.issubset(set(payload.get("bundle_tokens", [])))


def test_cosmo_cycle12_active_mode_changeset_endorsement_does_not_flip_adjudication() -> None:
    text = _read(TARGET_PATH) + "\n" + _read(STATE_PATH) + "\n" + _read(ROADMAP_PATH)
    assert "COSMO_BACKGROUND_ADJUDICATION: NOT_YET_DISCHARGED" in text
    assert "ADJUDICATION_FLIP_GRANTED" not in text
