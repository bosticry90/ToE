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
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_FULL_DISCHARGE_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qft_full_derivation_manual_flip_authorization_packet_cycle34_v0.json"
)

CYCLE34_PROGRESS_TOKEN = "QFT_FULL_DERIVATION_PROGRESS_CYCLE34_v0: MANUAL_FLIP_AUTHORIZATION_PACKET_LOCK_PINNED"
MANUAL_FLIP_PACKET_GATE_TOKEN = (
    "QFT_FULL_DERIVATION_MANUAL_FLIP_AUTHORIZATION_PACKET_GATE_v0: LOCKED_UNTIL_CYCLE33_REGISTRY_HASH_AND_TWO_KEY_SIGNOFF_PRESENT"
)
MANUAL_FLIP_PACKET_TWO_KEY_TOKEN = (
    "QFT_FULL_DERIVATION_MANUAL_FLIP_AUTHORIZATION_PACKET_TWO_KEY_v0: KEYA_PENDING_KEYB_PENDING"
)
ARTIFACT_TOKEN = (
    "QFT_FULL_DERIVATION_MANUAL_FLIP_AUTHORIZATION_PACKET_ARTIFACT_v0: qft_full_derivation_manual_flip_authorization_packet_cycle34_v0"
)
ARTIFACT_POINTER = "formal/output/qft_full_derivation_manual_flip_authorization_packet_cycle34_v0.json"
CYCLE34_GATE_PATH = "formal/python/tests/test_qft_full_derivation_manual_flip_authorization_packet_cycle34_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_cycle34_manual_flip_packet_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."
    assert ARTIFACT_PATH.exists(), "Missing cycle-34 manual flip-authorization packet artifact."


def test_qft_cycle34_manual_flip_packet_tokens_are_pinned_in_qft_docs() -> None:
    evol_text = _read(QFT_EVOL_TARGET_PATH)
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    for token in [
        CYCLE34_PROGRESS_TOKEN,
        MANUAL_FLIP_PACKET_GATE_TOKEN,
        MANUAL_FLIP_PACKET_TWO_KEY_TOKEN,
        CYCLE34_GATE_PATH,
    ]:
        assert token in evol_text, f"QFT evolution umbrella target missing cycle-34 token `{token}`."
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-34 token `{token}`."

    for token in [ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-34 packet token `{token}`."


def test_qft_cycle34_manual_flip_packet_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    for token in [
        CYCLE34_GATE_PATH,
        CYCLE34_PROGRESS_TOKEN,
        MANUAL_FLIP_PACKET_GATE_TOKEN,
        MANUAL_FLIP_PACKET_TWO_KEY_TOKEN,
    ]:
        assert token in roadmap_text, f"Roadmap authority surface must pin `{token}`."
        assert token in state_text, f"State authority surface must pin `{token}`."

    for token in [ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in state_text, f"State authority surface must pin `{token}`."


def test_qft_cycle34_manual_flip_packet_artifact_payload_is_consistent() -> None:
    payload = json.loads(_read(ARTIFACT_PATH))

    assert payload["artifact_id"] == "qft_full_derivation_manual_flip_authorization_packet_cycle34_v0"
    assert payload["target_id"] == "TARGET-QFT-FULL-DERIVATION-DISCHARGE-v0"
    assert payload["progress_token"] == CYCLE34_PROGRESS_TOKEN

    required_bundle_tokens = {
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE33_v0: FINAL_PREFLIP_EVIDENCE_REGISTRY_LOCK_PINNED",
        MANUAL_FLIP_PACKET_GATE_TOKEN,
        MANUAL_FLIP_PACKET_TWO_KEY_TOKEN,
        "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED",
    }
    assert required_bundle_tokens.issubset(set(payload.get("bundle_tokens", []))), (
        "Cycle-34 artifact bundle payload must contain required dependency and adjudication-lock tokens."
    )


def test_qft_cycle34_manual_flip_packet_does_not_flip_adjudication() -> None:
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    assert "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0" in discharge_text
