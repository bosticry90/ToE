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
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qft_full_derivation_adjudication_execution_guard_cycle35_v0.json"
)

CYCLE35_PROGRESS_TOKEN = "QFT_FULL_DERIVATION_PROGRESS_CYCLE35_v0: ADJUDICATION_EXECUTION_GUARD_LOCK_PINNED"
ADJUDICATION_EXECUTION_GUARD_GATE_TOKEN = (
    "QFT_FULL_DERIVATION_ADJUDICATION_EXECUTION_GUARD_GATE_v0: FLIP_FORBIDDEN_UNLESS_TWO_KEY_AUTHORIZED_AND_NONPENDING"
)
MANUAL_FLIP_AUTH_STATUS_GATE_TOKEN = (
    "QFT_FULL_DERIVATION_MANUAL_FLIP_AUTHORIZATION_STATUS_GATE_v0: KEYA_KEYB_MUST_BE_AUTHORIZED"
)
ARTIFACT_TOKEN = (
    "QFT_FULL_DERIVATION_ADJUDICATION_EXECUTION_GUARD_ARTIFACT_v0: qft_full_derivation_adjudication_execution_guard_cycle35_v0"
)
ARTIFACT_POINTER = "formal/output/qft_full_derivation_adjudication_execution_guard_cycle35_v0.json"
CYCLE35_GATE_PATH = "formal/python/tests/test_qft_full_derivation_adjudication_execution_guard_cycle35_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_cycle35_adjudication_execution_guard_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."
    assert ARTIFACT_PATH.exists(), "Missing cycle-35 adjudication execution guard artifact."


def test_qft_cycle35_adjudication_execution_guard_tokens_are_pinned_in_qft_docs() -> None:
    evol_text = _read(QFT_EVOL_TARGET_PATH)
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    for token in [
        CYCLE35_PROGRESS_TOKEN,
        ADJUDICATION_EXECUTION_GUARD_GATE_TOKEN,
        MANUAL_FLIP_AUTH_STATUS_GATE_TOKEN,
        CYCLE35_GATE_PATH,
    ]:
        assert token in evol_text, f"QFT evolution umbrella target missing cycle-35 token `{token}`."
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-35 token `{token}`."

    for token in [ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-35 guard token `{token}`."


def test_qft_cycle35_adjudication_execution_guard_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for token in [
        CYCLE35_GATE_PATH,
        CYCLE35_PROGRESS_TOKEN,
        ADJUDICATION_EXECUTION_GUARD_GATE_TOKEN,
        MANUAL_FLIP_AUTH_STATUS_GATE_TOKEN,
    ]:
        assert token in roadmap_text, f"Roadmap authority surface must pin `{token}`."
        assert token in state_text or token in inventory_text, (
            f"State/Inventory authority surface must pin `{token}`."
        )

    for token in [ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in state_text or token in inventory_text, (
            f"State/Inventory authority surface must pin `{token}`."
        )


def test_qft_cycle35_adjudication_execution_guard_artifact_payload_is_consistent() -> None:
    payload = json.loads(_read(ARTIFACT_PATH))

    assert payload["artifact_id"] == "qft_full_derivation_adjudication_execution_guard_cycle35_v0"
    assert payload["target_id"] == "TARGET-QFT-FULL-DERIVATION-DISCHARGE-v0"
    assert payload["progress_token"] == CYCLE35_PROGRESS_TOKEN

    required_bundle_tokens = {
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE34_v0: MANUAL_FLIP_AUTHORIZATION_PACKET_LOCK_PINNED",
        ADJUDICATION_EXECUTION_GUARD_GATE_TOKEN,
        MANUAL_FLIP_AUTH_STATUS_GATE_TOKEN,
        "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED",
    }
    assert required_bundle_tokens.issubset(set(payload.get("bundle_tokens", []))), (
        "Cycle-35 artifact bundle payload must contain required dependency and adjudication-lock tokens."
    )


def test_qft_cycle35_adjudication_execution_guard_does_not_flip_adjudication() -> None:
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    assert "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0" in discharge_text
