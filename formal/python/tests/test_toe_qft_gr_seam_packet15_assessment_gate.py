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
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_v0.md"
ASSESSMENT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet15_assessment_checkpoint_v0.json"
PACKET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET15_BOUNDED_EXECUTION_v0.md"
PACKET_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet15_bounded_execution_checkpoint_v0.json"
AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET15_AUTHORIZATION_v0.md"
AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet15_authorization_checkpoint_v0.json"
OBJECTIVE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
OBJECTIVE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qft_gr_seam_packet15_assessment_document_structure() -> None:
    text = _read(ASSESSMENT_DOC_PATH)
    required_markers = [
        "Assessment ID:",
        "Parent packet:",
        "Parent authorization:",
        "Parent objective:",
        "## Assessment Questions",
        "did packet15 satisfy its exact bounded target?",
        "target_satisfaction_verdict: YES_EXACT_TARGET_SATISFIED_v0",
        "physics_tightening_beyond_packet14_verdict: YES_REAL_TIGHTENING_VERIFIED_v0",
        "closure_sufficiency_witness_ambiguity_reduction_verdict: YES_RESIDUAL_AMBIGUITY_REDUCED_v0",
        "remaining_gap_narrower_than_objective_verdict: YES_NARROWER_THAN_OBJECTIVE_v0",
        "packet16_progress_verdict: GENUINE_PHYSICS_PROGRESS_IF_SINGLE_BOUNDED_TARGET_v0",
        "packet16_ladder_extension_verdict: REJECT_IF_MOMENTUM_EXTENSION_v0",
        "packet16_authorization_verdict: JUSTIFIED_CONDITIONAL_ON_SINGLE_BOUNDED_TARGET_v0",
        "packet16_exact_bounded_target:",
        "hold_refine_trigger_status: NOT_HIT_v0",
        "scalar_scope_backflow_status: NO_BACKFLOW_DETECTED_v0",
        "TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_STATUS_v0: ASSESSED_TARGET_SATISFACTION_VERIFIED_v0",
        "TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_GATE_v0: REQUIRED_PACKET15_ASSESSMENT_SCHEMA_AND_AUTHORITY_PARITY",
        "TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_ARTIFACT_v0: toe_qft_gr_seam_packet15_assessment_checkpoint_v0",
        "material_advancement_on_active_question: SATISFIED_v0",
        "remaining_target_is_narrower_than_objective: SATISFIED_v0",
        "hold_refine_condition_status: NOT_HIT_v0",
        "momentum_extension_rejection_status: ENFORCED_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet15 assessment doc missing marker: {marker}"


def test_qft_gr_seam_packet15_assessment_checkpoint_schema() -> None:
    artifact = _read_json(ASSESSMENT_CHECKPOINT_PATH)
    packet_artifact = _read_json(PACKET_CHECKPOINT_PATH)
    auth_artifact = _read_json(AUTH_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet15_assessment_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2B_QFT_GR_SEAM_PACKET15_ASSESSMENT"
    assert artifact.get("status") == "PACKET15_ASSESSMENT_COMPLETE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("assessment_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_v0.md"
    assert payload.get("parent_packet_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET15_BOUNDED_EXECUTION_v0.md"
    assert payload.get("parent_packet_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_packet15_bounded_execution_checkpoint_v0.json"
    )
    assert payload.get("parent_authorization_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET15_AUTHORIZATION_v0.md"
    assert payload.get("parent_authorization_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_packet15_authorization_checkpoint_v0.json"
    )
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    assert packet_artifact.get("status") == "PACKET15_EXECUTED_UNDER_AUTHORIZED_BOUNDED_TARGET_v0"
    assert auth_artifact.get("status") == "PACKET15_AUTHORIZATION_EXPLICIT_DECISION_COMPLETE_v0"

    sat = payload.get("target_satisfaction", {})
    assert sat.get("satisfied") is True
    assert sat.get("verdict") == "YES_EXACT_TARGET_SATISFIED_v0"
    assert sat.get("authorized_exact_target") == (
        "freeze_one_bounded_handoff_post_robustness_closure_sufficiency_discriminator_that_maps_packet14_closure_readiness_robustness_witness_to_a_single_non_scalar_expanding_closure_sufficiency_witness"
    )

    summary = payload.get("assessment_summary", {})
    assert summary.get("physics_tightening_beyond_packet14_verdict") == "YES_REAL_TIGHTENING_VERIFIED_v0"
    assert summary.get("closure_sufficiency_witness_ambiguity_reduction_verdict") == "YES_RESIDUAL_AMBIGUITY_REDUCED_v0"

    packet16 = payload.get("packet16_decision", {})
    assert packet16.get("authorized") is True
    assert packet16.get("progress_verdict") == "GENUINE_PHYSICS_PROGRESS_IF_SINGLE_BOUNDED_TARGET_v0"
    assert packet16.get("ladder_extension_verdict") == "REJECT_IF_MOMENTUM_EXTENSION_v0"
    assert packet16.get("verdict") == "JUSTIFIED_CONDITIONAL_ON_SINGLE_BOUNDED_TARGET_v0"
    assert packet16.get("hold_refine_trigger_status") == "NOT_HIT_v0"

    decision = payload.get("decision_rule_projection", {})
    assert decision.get("material_advancement_on_active_question") == "SATISFIED_v0"
    assert decision.get("remaining_target_is_narrower_than_objective") == "SATISFIED_v0"
    assert decision.get("scalar_scope_backflow_status") == "NO_BACKFLOW_DETECTED_v0"
    assert decision.get("hold_refine_condition_status") == "NOT_HIT_v0"
    assert decision.get("momentum_extension_rejection_status") == "ENFORCED_v0"

    scalar = payload.get("scalar_compliance", {})
    assert scalar.get("scalar_scope_backflow_status") == "NO_BACKFLOW_DETECTED_v0"


def test_qft_gr_seam_packet15_assessment_chain_consistency_and_authority_parity() -> None:
    assessment_text = _read(ASSESSMENT_DOC_PATH)
    packet_text = _read(PACKET_DOC_PATH)
    auth_text = _read(AUTH_DOC_PATH)
    objective_text = _read(OBJECTIVE_DOC_PATH)
    objective_checkpoint = _read_json(OBJECTIVE_CHECKPOINT_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in assessment_text
    assert q in packet_text
    assert q in auth_text
    assert q in objective_text
    assert objective_checkpoint["payload"].get("active_seam_question") == q

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_v0.md",
        "formal/output/toe_qft_gr_seam_packet15_assessment_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet15_assessment_gate.py",
    ]
    for ref in refs:
        assert ref in state_text, f"Missing packet15 assessment pointer in State_of_the_Theory.md: {ref}"
        assert ref in roadmap_text, f"Missing packet15 assessment pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_assessment = _extract_token(state_text, "TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_STATUS_v0")
    roadmap_assessment = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET15_ASSESSMENT_STATUS_v0")
    assert state_assessment == roadmap_assessment == "ASSESSED_TARGET_SATISFACTION_VERIFIED_v0"

    state_seam = _extract_token(state_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    roadmap_seam = _extract_token(roadmap_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"
