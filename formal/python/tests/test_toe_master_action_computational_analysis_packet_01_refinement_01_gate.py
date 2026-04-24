from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_master_action_computational_analysis_packet_01_refinement_01_v0.json"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-.:/]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_toe_master_action_computational_analysis_packet_01_refinement_01_gate() -> None:
    doc_text = _read(DOC_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))
    report = json.loads(_read(REPORT_PATH))
    payload = artifact.get("payload", {})
    criteria = report.get("criteria", {})
    numeric_summary = report.get("numeric_summary", {})
    summary = report.get("summary", {})

    assert _extract_token(doc_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(doc_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_AUTHORIZATION_CLASS_v0") == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert _extract_token(doc_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_DECISION_v0") == "INCONCLUSIVE_v0"

    assert artifact.get("artifact_id") == "toe_master_action_computational_analysis_packet_01_refinement_01_v0"
    assert payload.get("authorization_class") == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert payload.get("decision") == "INCONCLUSIVE_v0"
    assert payload.get("refinement_sequence") == 1
    assert payload.get("max_refinements_authorized") == 1
    assert payload.get("variation_id") == "PERTURBATION_WINDOW_TIGHTENING_v0"
    assert payload.get("baseline_value") == 0.03
    assert payload.get("refined_value") == 0.02
    assert payload.get("packet02_authorized") is False
    assert payload.get("gpu_backend_authorized") is False
    assert payload.get("lane_reopen_implication") is False
    assert payload.get("blocker_movement_claim") is False

    assert criteria.get("same_auxiliary_authorization_class") is True
    assert criteria.get("same_packet_level_inconclusive_ceiling") is True
    assert criteria.get("one_refinement_only") is True
    assert criteria.get("packet02_authorized") is False
    assert criteria.get("gpu_backend_authorized") is False
    assert criteria.get("lane_reopen_implication") is False
    assert criteria.get("blocker_movement_claim") is False
    assert criteria.get("regime_span_tightened") is True
    assert criteria.get("residual_nondegrading") is True
    assert criteria.get("spectral_radius_nonworsening") is True

    assert summary.get("packet_decision") == "INCONCLUSIVE_v0"
    assert summary.get("baseline_subordinate_disposition") == "REFINE_CANDIDATE_v0"
    assert summary.get("refinement_recommendation") == "RETAIN_REFINEMENT_v0"
    assert round(float(numeric_summary.get("refined_regime_limit_residual_span", 0.0)), 6) == 0.011237
    assert round(float(numeric_summary.get("refined_residual_norm", 0.0)), 6) == 0.036644
    assert round(float(numeric_summary.get("refined_spectral_radius", 0.0)), 6) == 0.990685

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_v0.md",
        "formal/output/toe_master_action_computational_analysis_packet_01_refinement_01_v0.json",
        "formal/output/reports/toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json",
        "formal/python/tests/test_toe_master_action_computational_analysis_packet_01_refinement_01_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text

