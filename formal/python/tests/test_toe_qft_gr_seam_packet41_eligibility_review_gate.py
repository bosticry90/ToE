from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md"
REVIEW_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0.json"
CONVERGENCE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
CONVERGENCE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md"
ASSESSMENT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet40_assessment_checkpoint_v0.json"
OBJECTIVE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PACKET41_AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET41_AUTHORIZATION_v0.md"
PACKET41_AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_authorization_checkpoint_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qft_gr_seam_packet41_eligibility_review_document_structure() -> None:
    text = _read(REVIEW_DOC_PATH)
    required_markers = [
        "Review ID:",
        "Parent assessment:",
        "Parent convergence criterion:",
        "## Review Inputs",
        "## Eligibility Review Questions",
        "seam_gap_still_measurably_shrinking: NOT_YET_DEMONSTRATED_v0",
        "expected_marginal_gain_above_threshold: NOT_YET_DEMONSTRATED_v0",
        "stagnation_or_semantic_reencoding_risk: UNRESOLVED_PENDING_CONCRETE_PACKET41_TARGET_v0",
        "remaining_gap_still_narrower_than_objective: SATISFIED_v0",
        "## Packet41 Readiness Assessment",
        "current_packet41_gain_statement_status: MISSING_v0",
        "current_packet41_stagnation_clearance_status: NOT_YET_DEMONSTRATED_v0",
        "current_packet41_convergence_binding_status: INCOMPLETE_v0",
        "## Disposition Decision",
        "disposition_hold: ACTIVE",
        "review_decision_outcome: HOLD_PACKET41_PENDING_CONCRETE_SEAM_LEVEL_GAIN_EVIDENCE_v0",
        "## Required Conditions To Exit Hold",
        "packet41_authorization_freeze_status: ENFORCED_v0",
        "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0",
        "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_DISPOSITION_v0: HOLD_v0",
        "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_GATE_v0: REQUIRED_PACKET41_ELIGIBILITY_REVIEW_SCHEMA_AND_FREEZE_ENFORCEMENT",
        "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_ARTIFACT_v0: toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet41 eligibility review doc missing marker: {marker}"


def test_qft_gr_seam_packet41_eligibility_review_checkpoint_schema_and_hold_disposition() -> None:
    artifact = _read_json(REVIEW_CHECKPOINT_PATH)
    assessment_artifact = _read_json(ASSESSMENT_CHECKPOINT_PATH)
    convergence_artifact = _read_json(CONVERGENCE_CHECKPOINT_PATH)
    objective_artifact = _read_json(OBJECTIVE_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2U_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW"
    assert artifact.get("status") == "PACKET41_ELIGIBILITY_REVIEW_COMPLETE_HOLD_v0"

    payload = artifact.get("payload", {})
    assert payload.get("review_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md"
    assert payload.get("parent_assessment_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md"
    assert payload.get("parent_convergence_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    questions = payload.get("eligibility_review_questions", {})
    assert questions.get("seam_gap_still_measurably_shrinking") == "NOT_YET_DEMONSTRATED_v0"
    assert questions.get("expected_marginal_gain_above_threshold") == "NOT_YET_DEMONSTRATED_v0"
    assert questions.get("stagnation_or_semantic_reencoding_risk") == "UNRESOLVED_PENDING_CONCRETE_PACKET41_TARGET_v0"
    assert questions.get("remaining_gap_still_narrower_than_objective") == "SATISFIED_v0"

    readiness = payload.get("packet41_readiness_assessment", {})
    assert readiness.get("current_packet41_gain_statement_status") == "MISSING_v0"
    assert readiness.get("current_packet41_stagnation_clearance_status") == "NOT_YET_DEMONSTRATED_v0"
    assert readiness.get("current_packet41_convergence_binding_status") == "INCOMPLETE_v0"

    disposition = payload.get("disposition_decision", {})
    assert disposition.get("disposition_authorize") == "INACTIVE"
    assert disposition.get("disposition_hold") == "ACTIVE"
    assert disposition.get("disposition_fork") == "INACTIVE"
    assert disposition.get("disposition_terminate") == "INACTIVE"
    assert disposition.get("review_decision_outcome") == "HOLD_PACKET41_PENDING_CONCRETE_SEAM_LEVEL_GAIN_EVIDENCE_v0"

    assert assessment_artifact.get("status") == "PACKET40_ASSESSMENT_COMPLETE_CONDITIONAL_PACKET41_READINESS_ONLY_v0"
    assert convergence_artifact.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"
    assert objective_artifact.get("payload", {}).get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"


def test_qft_gr_seam_packet41_eligibility_review_authority_parity_and_freeze_enforcement() -> None:
    review_text = _read(REVIEW_DOC_PATH)
    assessment_text = _read(ASSESSMENT_DOC_PATH)
    convergence_text = _read(CONVERGENCE_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in review_text
    assert q in assessment_text
    assert q in convergence_text

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md",
        "formal/output/toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet41_eligibility_review_gate.py",
    ]
    for ref in refs:
        assert ref in state_text, f"Missing packet41 eligibility review pointer in State_of_the_Theory.md: {ref}"
        assert ref in roadmap_text, f"Missing packet41 eligibility review pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token(state_text, "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_STATUS_v0")
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_STATUS_v0")
    assert state_status == roadmap_status == "REVIEW_COMPLETE_HOLD_v0"

    state_disposition = _extract_token(state_text, "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_DISPOSITION_v0")
    roadmap_disposition = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_DISPOSITION_v0")
    assert state_disposition == roadmap_disposition == "HOLD_v0"

    assert not PACKET41_AUTH_DOC_PATH.exists(), "Packet41 authorization doc must not exist during hold disposition"
    assert not PACKET41_AUTH_CHECKPOINT_PATH.exists(), "Packet41 authorization checkpoint must not exist during hold disposition"
