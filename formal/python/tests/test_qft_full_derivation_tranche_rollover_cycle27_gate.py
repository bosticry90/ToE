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
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_FULL_DISCHARGE_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qft_full_derivation_tranche_rollover_gate_bundle_cycle27_v0.json"

CYCLE27_PROGRESS_TOKEN = "QFT_FULL_DERIVATION_PROGRESS_CYCLE27_v0: TRANCHE_ROLLOVER_LEGACY_FORBID_GATE_BUNDLE_PINNED"
TRANCHE_ROLLOVER_GATE_TOKEN = "QFT_FULL_DERIVATION_TRANCHE_ROLLOVER_GATE_v0: CYCLE26_TO_CYCLE27_HARDENING_ROUTE_ONLY"
LEGACY_FORBID_GATE_TOKEN = "QFT_FULL_DERIVATION_LEGACY_ROUTE_FORBID_GATE_v0: NO_LEGACY_PROMOTION_OR_ADJUDICATION_SHORTCUT"
TRANSITION_POLICY_TOKEN = (
    "QFT_FULL_DERIVATION_DISCHARGE_TRANSITION_POLICY_v0: LOCKED_UNTIL_EXIT_ROW_CRITERIA_AND_PREDISCHARGE_BUNDLE"
)
ARTIFACT_TOKEN = (
    "QFT_FULL_DERIVATION_TRANCHE_ROLLOVER_GATE_BUNDLE_ARTIFACT_v0: qft_full_derivation_tranche_rollover_gate_bundle_cycle27_v0"
)
ARTIFACT_POINTER = "formal/output/qft_full_derivation_tranche_rollover_gate_bundle_cycle27_v0.json"
CYCLE27_GATE_PATH = "formal/python/tests/test_qft_full_derivation_tranche_rollover_cycle27_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_cycle27_rollover_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."
    assert ARTIFACT_PATH.exists(), "Missing cycle-27 tranche-rollover artifact bundle."


def test_qft_cycle27_rollover_tokens_are_pinned_in_qft_docs() -> None:
    evol_text = _read(QFT_EVOL_TARGET_PATH)
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    for token in [
        CYCLE27_PROGRESS_TOKEN,
        TRANCHE_ROLLOVER_GATE_TOKEN,
        LEGACY_FORBID_GATE_TOKEN,
        CYCLE27_GATE_PATH,
    ]:
        assert token in evol_text, f"QFT evolution umbrella target missing cycle-27 token `{token}`."
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-27 token `{token}`."

    for token in [TRANSITION_POLICY_TOKEN, ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-27 closure token `{token}`."


def test_qft_cycle27_rollover_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for token in [
        CYCLE27_GATE_PATH,
        CYCLE27_PROGRESS_TOKEN,
        TRANCHE_ROLLOVER_GATE_TOKEN,
        LEGACY_FORBID_GATE_TOKEN,
    ]:
        assert token in roadmap_text, f"Roadmap authority surface must pin `{token}`."
        assert token in state_text or token in inventory_text, (
            f"State/Inventory authority surface must pin `{token}`."
        )

    for token in [TRANSITION_POLICY_TOKEN, ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in state_text or token in inventory_text, (
            f"State/Inventory authority surface must pin `{token}`."
        )


def test_qft_cycle27_rollover_artifact_payload_is_consistent() -> None:
    payload = json.loads(_read(ARTIFACT_PATH))

    assert payload["artifact_id"] == "qft_full_derivation_tranche_rollover_gate_bundle_cycle27_v0"
    assert payload["target_id"] == "TARGET-QFT-FULL-DERIVATION-DISCHARGE-v0"
    assert payload["progress_token"] == CYCLE27_PROGRESS_TOKEN

    required_bundle_tokens = {
        TRANCHE_ROLLOVER_GATE_TOKEN,
        LEGACY_FORBID_GATE_TOKEN,
        TRANSITION_POLICY_TOKEN,
        "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED",
    }
    assert required_bundle_tokens.issubset(set(payload.get("bundle_tokens", []))), (
        "Cycle-27 artifact bundle payload must contain all required rollover/legacy-forbid/adjudication-lock tokens."
    )


def test_qft_cycle27_rollover_does_not_flip_adjudication() -> None:
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    assert "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0" in discharge_text
