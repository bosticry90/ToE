from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_FULL_DISCHARGE_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qft_full_derivation_final_prefip_evidence_registry_cycle33_v0.json"
)

CYCLE33_PROGRESS_TOKEN = "QFT_FULL_DERIVATION_PROGRESS_CYCLE33_v0: FINAL_PREFLIP_EVIDENCE_REGISTRY_LOCK_PINNED"
EVIDENCE_REGISTRY_GATE_TOKEN = (
    "QFT_FULL_DERIVATION_FINAL_PREFLIP_EVIDENCE_REGISTRY_GATE_v0: LOCKED_UNTIL_ALL_REQUIRED_BUNDLES_PRESENT_AND_HASH_PINNED"
)
EVIDENCE_REQUIRED_BUNDLES_TOKEN = (
    "QFT_FULL_DERIVATION_FINAL_PREFLIP_EVIDENCE_REQUIRED_BUNDLES_v0: CYCLE27_ROLLOVER;CYCLE28_EXIT_ROW;CYCLE29_PREDISCHARGE_TRANSITION;CYCLE30_READINESS;CYCLE31_ADJUDICATION_CRITERIA;CYCLE32_FLIP_PACKET"
)
ARTIFACT_TOKEN = (
    "QFT_FULL_DERIVATION_FINAL_PREFLIP_EVIDENCE_REGISTRY_ARTIFACT_v0: qft_full_derivation_final_prefip_evidence_registry_cycle33_v0"
)
ARTIFACT_POINTER = "formal/output/qft_full_derivation_final_prefip_evidence_registry_cycle33_v0.json"
CYCLE33_GATE_PATH = "formal/python/tests/test_qft_full_derivation_final_prefip_evidence_registry_cycle33_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_cycle33_evidence_registry_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."
    assert ARTIFACT_PATH.exists(), "Missing cycle-33 final preflip evidence registry artifact."


def test_qft_cycle33_evidence_registry_tokens_are_pinned_in_qft_docs() -> None:
    evol_text = _read(QFT_EVOL_TARGET_PATH)
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    for token in [
        CYCLE33_PROGRESS_TOKEN,
        EVIDENCE_REGISTRY_GATE_TOKEN,
        EVIDENCE_REQUIRED_BUNDLES_TOKEN,
        CYCLE33_GATE_PATH,
    ]:
        assert token in evol_text, f"QFT evolution umbrella target missing cycle-33 token `{token}`."
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-33 token `{token}`."

    for token in [ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-33 registry token `{token}`."


def test_qft_cycle33_evidence_registry_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for token in [
        CYCLE33_GATE_PATH,
        CYCLE33_PROGRESS_TOKEN,
        EVIDENCE_REGISTRY_GATE_TOKEN,
        EVIDENCE_REQUIRED_BUNDLES_TOKEN,
    ]:
        assert token in roadmap_text, f"Roadmap authority surface must pin `{token}`."
        assert token in state_text or token in inventory_text, (
            f"State/Inventory authority surface must pin `{token}`."
        )

    for token in [ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in state_text or token in inventory_text, (
            f"State/Inventory authority surface must pin `{token}`."
        )


def test_qft_cycle33_evidence_registry_artifact_payload_is_consistent() -> None:
    payload = json.loads(_read(ARTIFACT_PATH))

    assert payload["artifact_id"] == "qft_full_derivation_final_prefip_evidence_registry_cycle33_v0"
    assert payload["target_id"] == "TARGET-QFT-FULL-DERIVATION-DISCHARGE-v0"
    assert payload["progress_token"] == CYCLE33_PROGRESS_TOKEN

    required_bundle_tokens = {
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE32_v0: FLIP_DECISION_PACKET_LOCK_PINNED",
        EVIDENCE_REGISTRY_GATE_TOKEN,
        EVIDENCE_REQUIRED_BUNDLES_TOKEN,
        "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED",
    }
    assert required_bundle_tokens.issubset(set(payload.get("bundle_tokens", []))), (
        "Cycle-33 artifact bundle payload must contain required dependency and adjudication-lock tokens."
    )


def test_qft_cycle33_evidence_registry_does_not_flip_adjudication() -> None:
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    assert "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0" in discharge_text
