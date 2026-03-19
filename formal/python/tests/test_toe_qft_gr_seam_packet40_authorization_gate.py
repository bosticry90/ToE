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
AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_v0.md"
AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet40_authorization_checkpoint_v0.json"
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET39_ASSESSMENT_v0.md"
ASSESSMENT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet39_assessment_checkpoint_v0.json"
OBJECTIVE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
OBJECTIVE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token_from_surfaces(texts: list[str], token_name: str) -> str:
    for text in texts:
        m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
        if m is not None:
            return m.group(1)
    assert False, f"Missing token `{token_name}` across authority surfaces."


def test_qft_gr_seam_packet40_authorization_document_structure() -> None:
    text = _read(AUTH_DOC_PATH)
    required_markers = [
        "Authorization ID:",
        "Parent assessment:",
        "Parent objective:",
        "## Decision Branches",
        "branch_a_authorize_packet40: ACTIVE",
        "branch_b_hold_and_refine_objective: INACTIVE",
        "## Decision Preconditions (from packet39 assessment)",
        "material_advancement_on_active_question: SATISFIED_v0",
        "remaining_target_is_narrower_than_objective: SATISFIED_v0",
        "scalar_scope_backflow_status: NO_BACKFLOW_DETECTED_v0",
        "hold_refine_condition_status: NOT_HIT_v0",
        "decision_outcome: AUTHORIZE_PACKET40_BOUNDED_TARGET_v0",
        "packet40_physics_quantity_tightened:",
        "packet40_discriminator_strengthening_requirement:",
        "packet40_ambiguity_reduction_requirement:",
        "packet40_non_repetition_clause:",
        "TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_STATUS_v0: AUTHORIZED_WITH_SINGLE_BOUNDED_TARGET_v0",
        "TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_GATE_v0: REQUIRED_PACKET40_AUTHORIZATION_SCHEMA_AND_AUTHORITY_PARITY",
        "TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_ARTIFACT_v0: toe_qft_gr_seam_packet40_authorization_checkpoint_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet40 authorization doc missing marker: {marker}"


def test_qft_gr_seam_packet40_authorization_checkpoint_schema_and_preconditions() -> None:
    artifact = _read_json(AUTH_CHECKPOINT_PATH)
    assessment_artifact = _read_json(ASSESSMENT_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet40_authorization_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_1AM_QFT_GR_SEAM_PACKET40_AUTHORIZATION"
    assert artifact.get("status") == "PACKET40_AUTHORIZATION_EXPLICIT_DECISION_COMPLETE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("authorization_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_v0.md"
    assert payload.get("parent_assessment_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET39_ASSESSMENT_v0.md"
    assert payload.get("parent_assessment_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_packet39_assessment_checkpoint_v0.json"
    )
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    projection = assessment_artifact.get("payload", {}).get("packet40_projection", {})
    readiness = projection.get("authorization_readiness", {})
    assert readiness.get("readiness_state") == "CONDITIONAL_READINESS_ONLY_v0"

    pre_from_assessment = projection.get("authorization_preconditions", {})
    assert pre_from_assessment.get("material_advancement_on_active_question") == "SATISFIED_v0"
    assert pre_from_assessment.get("remaining_target_is_narrower_than_objective") == "SATISFIED_v0"
    assert pre_from_assessment.get("scalar_scope_backflow_status") == "NO_BACKFLOW_DETECTED_v0"
    assert pre_from_assessment.get("hold_refine_condition_status") == "NOT_HIT_v0"

    pre = payload.get("preconditions_from_packet39_assessment", {})
    assert pre.get("material_advancement_on_active_question") == "SATISFIED_v0"
    assert pre.get("remaining_target_is_narrower_than_objective") == "SATISFIED_v0"
    assert pre.get("scalar_scope_backflow_status") == "NO_BACKFLOW_DETECTED_v0"
    assert pre.get("hold_refine_condition_status") == "NOT_HIT_v0"

    decision = payload.get("authorization_decision", {})
    assert decision.get("authorized") is True
    assert decision.get("decision_outcome") == "AUTHORIZE_PACKET40_BOUNDED_TARGET_v0"
    assert decision.get("status") == "AUTHORIZED_WITH_SINGLE_BOUNDED_TARGET_v0"

    bounded = payload.get("packet40_bounded_target", {})
    assert bounded.get("exact_target") == (
        "freeze_one_bounded_handoff_post_contradiction_closure_refutation_resilience_discriminator_that_maps_packet39_closure_contradiction_screen_witness_to_a_single_non_scalar_expanding_closure_refutation_resilience_witness"
    )
    assert bounded.get("discriminator_strengthening_requirement") == (
        "criterion_level_post_contradiction_refutation_resilience_discrimination_beyond_packet39_contradiction_screen_witness_qualification_required"
    )
    assert bounded.get("ambiguity_reduction_requirement") == (
        "packet40_valid_only_if_residual_interface_ambiguity_reduced_via_new_refutation_resilience_discriminative_content"
    )
    assert bounded.get("non_repetition_clause") == (
        "packet40_invalid_if_only_packet39_contradiction_screen_witness_reencoded_without_new_refutation_resilience_discriminative_content"
    )


def test_qft_gr_seam_packet40_authorization_chain_consistency_and_authority_parity() -> None:
    auth_text = _read(AUTH_DOC_PATH)
    assessment_text = _read(ASSESSMENT_DOC_PATH)
    objective_text = _read(OBJECTIVE_DOC_PATH)
    objective_checkpoint = _read_json(OBJECTIVE_CHECKPOINT_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in auth_text
    assert q in assessment_text
    assert q in objective_text
    assert objective_checkpoint["payload"].get("active_seam_question") == q

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_v0.md",
        "formal/output/toe_qft_gr_seam_packet40_authorization_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet40_authorization_gate.py",
    ]
    for ref in refs:
        assert any(ref in text for text in (state_text, inventory_text, roadmap_text)), (
            f"Missing packet40 authorization pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet40 authorization pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_auth = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_STATUS_v0",
    )
    roadmap_auth = _extract_token_from_surfaces([roadmap_text], "TOE_QFT_GR_SEAM_PACKET40_AUTHORIZATION_STATUS_v0")
    assert state_auth == roadmap_auth == "AUTHORIZED_WITH_SINGLE_BOUNDED_TARGET_v0"

    state_seam = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0",
    )
    roadmap_seam = _extract_token_from_surfaces([roadmap_text], "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"
