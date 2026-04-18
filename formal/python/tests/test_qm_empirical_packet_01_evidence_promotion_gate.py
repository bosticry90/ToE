from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
PROMOTION_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md"
QM_PACKET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_01_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_empirical_comparison_packet_01_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qm_empirical_packet_01_evidence_promotion_gate() -> None:
    promo_text = _read(PROMOTION_DOC_PATH)
    qm_doc_text = _read(QM_PACKET_DOC_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))
    payload = artifact.get("payload", {})

    assert _extract_token(promo_text, "QM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(promo_text, "QM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_TARGET_TIER_v0") == "INTERMEDIATE_v0"
    assert _extract_token(promo_text, "QM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_GATE_v0") == "CRITERIA_AND_POINTERS_REQUIRED"
    assert _extract_token(promo_text, "QM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_CRITERIA_v0") == "CYCLE01_CRITERIA_PINNED"

    assert _extract_token(promo_text, "QM_EMPIRICAL_PACKET_01_CRITERION_RESIDUAL_OBSERVABLE_LINK_v0") == "SATISFIED_v0"
    assert _extract_token(promo_text, "QM_EMPIRICAL_PACKET_01_CRITERION_COMPARATOR_MAPPING_PIN_v0") == "SATISFIED_v0"
    assert _extract_token(promo_text, "QM_EMPIRICAL_PACKET_01_CRITERION_UNCERTAINTY_BUDGET_BOUNDED_v0") == "SATISFIED_v0"

    assert _extract_token(qm_doc_text, "QM_EMPIRICAL_PACKET_01_EVIDENCE_TIER_v0") == "INTERMEDIATE_v0"
    assert payload.get("evidence_tier") == "INTERMEDIATE_v0"

    criteria = payload.get("evidence_promotion_criteria")
    assert isinstance(criteria, dict), "Missing evidence_promotion_criteria payload object."
    assert criteria.get("residual_observable_linked") is True
    assert criteria.get("comparator_mapping_pinned") is True
    assert criteria.get("uncertainty_budget_bounded") is True

    uncertainty = str(payload.get("uncertainty_annotation", "")).lower()
    assert "scaffold" not in uncertainty, "INTERMEDIATE tier must not retain scaffold uncertainty label."

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md",
        "formal/python/tests/test_qm_empirical_packet_01_evidence_promotion_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text
