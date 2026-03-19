from __future__ import annotations

import json
import re
from pathlib import Path

from qft_gr_seam_registry_helpers import get_packet_entry
from qft_gr_seam_registry_helpers import get_repo_root
from qft_gr_seam_registry_helpers import load_registry
from qft_gr_seam_registry_helpers import resolve_rel_path


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_compact_state_or_inventory(state_text: str, inventory_text: str, token_name: str) -> str:
    if re.search(rf"\b{re.escape(token_name)}\s*:\s*", state_text):
        return _extract_token(state_text, token_name)
    return _extract_token(inventory_text, token_name)


def run_packet_eligibility_review_checks(packet_id: int, gate_rel_path: str) -> None:
    repo_root = get_repo_root(Path(__file__))
    registry = load_registry(Path(__file__))
    packet = get_packet_entry(registry, packet_id=packet_id)

    review_doc_rel = packet.get("docs", {}).get("eligibility_review")
    review_checkpoint_rel = packet.get("checkpoints", {}).get("eligibility_review")

    assert isinstance(review_doc_rel, str) and review_doc_rel
    assert isinstance(review_checkpoint_rel, str) and review_checkpoint_rel

    review_doc_path = resolve_rel_path(repo_root, review_doc_rel)
    review_checkpoint_path = resolve_rel_path(repo_root, review_checkpoint_rel)

    convergence_doc_path = repo_root / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
    convergence_checkpoint_path = repo_root / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
    assessment_doc_path = repo_root / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md"
    assessment_checkpoint_path = repo_root / "formal" / "output" / "toe_qft_gr_seam_packet40_assessment_checkpoint_v0.json"
    objective_checkpoint_path = repo_root / "formal" / "output" / "toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json"
    state_path = repo_root / "State_of_the_Theory.md"
    inventory_path = repo_root / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
    roadmap_path = repo_root / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
    auth_doc_path = repo_root / "formal" / "docs" / "paper" / f"TOE_QFT_GR_SEAM_PACKET{packet_id}_AUTHORIZATION_v0.md"
    auth_checkpoint_path = repo_root / "formal" / "output" / f"toe_qft_gr_seam_packet{packet_id}_authorization_checkpoint_v0.json"

    review_text = _read(review_doc_path)
    assessment_text = _read(assessment_doc_path)
    convergence_text = _read(convergence_doc_path)
    state_text = _read(state_path)
    inventory_text = _read(inventory_path)
    roadmap_text = _read(roadmap_path)

    required_markers = [
        "Review ID:",
        "Parent assessment:",
        "Parent convergence criterion:",
        "## Review Inputs",
        "## Eligibility Review Questions",
        "seam_gap_still_measurably_shrinking: NOT_YET_DEMONSTRATED_v0",
        "expected_marginal_gain_above_threshold: NOT_YET_DEMONSTRATED_v0",
        f"stagnation_or_semantic_reencoding_risk: UNRESOLVED_PENDING_CONCRETE_PACKET{packet_id}_TARGET_v0",
        "remaining_gap_still_narrower_than_objective: SATISFIED_v0",
        f"## Packet{packet_id} Readiness Assessment",
        f"current_packet{packet_id}_gain_statement_status: MISSING_v0",
        f"current_packet{packet_id}_stagnation_clearance_status: NOT_YET_DEMONSTRATED_v0",
        f"current_packet{packet_id}_convergence_binding_status: INCOMPLETE_v0",
        "## Disposition Decision",
        "disposition_hold: ACTIVE",
        f"review_decision_outcome: HOLD_PACKET{packet_id}_PENDING_CONCRETE_SEAM_LEVEL_GAIN_EVIDENCE_v0",
        "## Required Conditions To Exit Hold",
        f"packet{packet_id}_authorization_freeze_status: ENFORCED_v0",
        f"TOE_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0",
        f"TOE_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_DISPOSITION_v0: HOLD_v0",
        f"TOE_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_GATE_v0: REQUIRED_PACKET{packet_id}_ELIGIBILITY_REVIEW_SCHEMA_AND_FREEZE_ENFORCEMENT",
        f"TOE_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_ARTIFACT_v0: toe_qft_gr_seam_packet{packet_id}_eligibility_review_checkpoint_v0",
    ]
    for marker in required_markers:
        assert marker in review_text, f"Packet{packet_id} eligibility review doc missing marker: {marker}"

    artifact = _read_json(review_checkpoint_path)
    assessment_artifact = _read_json(assessment_checkpoint_path)
    convergence_artifact = _read_json(convergence_checkpoint_path)
    objective_artifact = _read_json(objective_checkpoint_path)

    assert artifact.get("artifact_id") == f"toe_qft_gr_seam_packet{packet_id}_eligibility_review_checkpoint_v0"
    assert artifact.get("phase") == f"PHASE_2U_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_REVIEW"
    assert artifact.get("status") == f"PACKET{packet_id}_ELIGIBILITY_REVIEW_COMPLETE_HOLD_v0"

    payload = artifact.get("payload", {})
    assert payload.get("review_doc_path") == review_doc_rel
    assert payload.get("parent_assessment_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md"
    assert payload.get("parent_convergence_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    questions = payload.get("eligibility_review_questions", {})
    assert questions.get("seam_gap_still_measurably_shrinking") == "NOT_YET_DEMONSTRATED_v0"
    assert questions.get("expected_marginal_gain_above_threshold") == "NOT_YET_DEMONSTRATED_v0"
    assert questions.get("stagnation_or_semantic_reencoding_risk") == (
        f"UNRESOLVED_PENDING_CONCRETE_PACKET{packet_id}_TARGET_v0"
    )
    assert questions.get("remaining_gap_still_narrower_than_objective") == "SATISFIED_v0"

    readiness = payload.get(f"packet{packet_id}_readiness_assessment", {})
    assert readiness.get(f"current_packet{packet_id}_gain_statement_status") == "MISSING_v0"
    assert readiness.get(f"current_packet{packet_id}_stagnation_clearance_status") == "NOT_YET_DEMONSTRATED_v0"
    assert readiness.get(f"current_packet{packet_id}_convergence_binding_status") == "INCOMPLETE_v0"

    disposition = payload.get("disposition_decision", {})
    assert disposition.get("disposition_authorize") == "INACTIVE"
    assert disposition.get("disposition_hold") == "ACTIVE"
    assert disposition.get("disposition_fork") == "INACTIVE"
    assert disposition.get("disposition_terminate") == "INACTIVE"
    assert disposition.get("review_decision_outcome") == (
        f"HOLD_PACKET{packet_id}_PENDING_CONCRETE_SEAM_LEVEL_GAIN_EVIDENCE_v0"
    )

    assert assessment_artifact.get("status") == "PACKET40_ASSESSMENT_COMPLETE_CONDITIONAL_PACKET41_READINESS_ONLY_v0"
    assert convergence_artifact.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"
    assert objective_artifact.get("payload", {}).get("active_seam_question") == (
        "stress_energy_to_weak_curvature_handoff_strengthening"
    )

    assert "stress_energy_to_weak_curvature_handoff_strengthening" in review_text
    assert "stress_energy_to_weak_curvature_handoff_strengthening" in assessment_text
    assert "stress_energy_to_weak_curvature_handoff_strengthening" in convergence_text

    refs = [review_doc_rel, review_checkpoint_rel, gate_rel_path]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing packet{packet_id} eligibility review pointer in compact-State or central inventory: {ref}"
        )
        assert ref in roadmap_text, (
            f"Missing packet{packet_id} eligibility review pointer in PHYSICS_ROADMAP_v0.md: {ref}"
        )

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        f"TOE_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_STATUS_v0",
    )
    roadmap_status = _extract_token(
        roadmap_text,
        f"TOE_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_STATUS_v0",
    )
    assert state_status == roadmap_status == "REVIEW_COMPLETE_HOLD_v0"

    state_disposition = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        f"TOE_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_DISPOSITION_v0",
    )
    roadmap_disposition = _extract_token(
        roadmap_text,
        f"TOE_QFT_GR_SEAM_PACKET{packet_id}_ELIGIBILITY_DISPOSITION_v0",
    )
    assert state_disposition == roadmap_disposition == "HOLD_v0"

    assert not auth_doc_path.exists(), (
        f"Packet{packet_id} authorization doc must not exist during hold disposition"
    )
    assert not auth_checkpoint_path.exists(), (
        f"Packet{packet_id} authorization checkpoint must not exist during hold disposition"
    )
