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
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qft_full_derivation_adjudication_criteria_bundle_cycle31_v0.json"

CYCLE31_PROGRESS_TOKEN = "QFT_FULL_DERIVATION_PROGRESS_CYCLE31_v0: ADJUDICATION_CRITERIA_BUNDLE_LOCK_PINNED"
ADJUDICATION_CRITERIA_GATE_TOKEN = (
    "QFT_FULL_DERIVATION_ADJUDICATION_CRITERIA_GATE_v0: LOCKED_UNTIL_ALL_EXIT_ROWS_AND_TRANSITION_BUNDLES_COMPLETE"
)
INEVITABILITY_CRITERIA_GATE_TOKEN = (
    "QFT_FULL_DERIVATION_INEVITABILITY_CRITERIA_GATE_v0: LOCKED_UNTIL_COUNTERFACTUAL_AND_INDEPENDENT_NECESSITY_BUNDLES_COMPLETE"
)
ARTIFACT_TOKEN = (
    "QFT_FULL_DERIVATION_ADJUDICATION_CRITERIA_BUNDLE_ARTIFACT_v0: qft_full_derivation_adjudication_criteria_bundle_cycle31_v0"
)
ARTIFACT_POINTER = "formal/output/qft_full_derivation_adjudication_criteria_bundle_cycle31_v0.json"
CYCLE31_GATE_PATH = "formal/python/tests/test_qft_full_derivation_adjudication_criteria_cycle31_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_cycle31_adjudication_criteria_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."
    assert ARTIFACT_PATH.exists(), "Missing cycle-31 adjudication-criteria artifact bundle."


def test_qft_cycle31_adjudication_criteria_tokens_are_pinned_in_qft_docs() -> None:
    evol_text = _read(QFT_EVOL_TARGET_PATH)
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    for token in [
        CYCLE31_PROGRESS_TOKEN,
        ADJUDICATION_CRITERIA_GATE_TOKEN,
        INEVITABILITY_CRITERIA_GATE_TOKEN,
        CYCLE31_GATE_PATH,
    ]:
        assert token in evol_text, f"QFT evolution umbrella target missing cycle-31 token `{token}`."
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-31 token `{token}`."

    for token in [ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-31 criteria token `{token}`."


def test_qft_cycle31_adjudication_criteria_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for token in [
        CYCLE31_GATE_PATH,
        CYCLE31_PROGRESS_TOKEN,
        ADJUDICATION_CRITERIA_GATE_TOKEN,
        INEVITABILITY_CRITERIA_GATE_TOKEN,
    ]:
        assert token in roadmap_text, f"Roadmap authority surface must pin `{token}`."
        assert token in state_text or token in inventory_text, (
            f"State/Inventory authority surface must pin `{token}`."
        )

    for token in [ARTIFACT_TOKEN, ARTIFACT_POINTER]:
        assert token in state_text or token in inventory_text, (
            f"State/Inventory authority surface must pin `{token}`."
        )


def test_qft_cycle31_adjudication_criteria_artifact_payload_is_consistent() -> None:
    payload = json.loads(_read(ARTIFACT_PATH))

    assert payload["artifact_id"] == "qft_full_derivation_adjudication_criteria_bundle_cycle31_v0"
    assert payload["target_id"] == "TARGET-QFT-FULL-DERIVATION-DISCHARGE-v0"
    assert payload["progress_token"] == CYCLE31_PROGRESS_TOKEN

    required_bundle_tokens = {
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE30_v0: DISCHARGE_TRANSITION_READINESS_BUNDLE_LOCK_PINNED",
        ADJUDICATION_CRITERIA_GATE_TOKEN,
        INEVITABILITY_CRITERIA_GATE_TOKEN,
        "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED",
    }
    assert required_bundle_tokens.issubset(set(payload.get("bundle_tokens", []))), (
        "Cycle-31 artifact bundle payload must contain required dependency and adjudication-lock tokens."
    )


def test_qft_cycle31_adjudication_criteria_does_not_flip_adjudication() -> None:
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    assert "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED" in discharge_text
    assert "QFT_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0" in discharge_text
    assert "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0" in discharge_text
