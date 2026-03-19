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
AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_v0.md"
AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet21_authorization_checkpoint_v0.json"
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET20_ASSESSMENT_v0.md"
ASSESSMENT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet20_assessment_checkpoint_v0.json"
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
    assert False, f"Missing token `{token_name}`."


def test_qft_gr_seam_packet21_authorization_document_structure() -> None:
    text = _read(AUTH_DOC_PATH)
    required_markers = [
        "Authorization ID:",
        "Parent assessment:",
        "Parent objective:",
        "## Decision Branches",
        "branch_a_authorize_packet21: ACTIVE",
        "branch_b_hold_and_refine_objective: INACTIVE",
        "## Decision Preconditions (from packet20 assessment)",
        "material_advancement_on_active_question: SATISFIED_v0",
        "remaining_target_is_narrower_than_objective: SATISFIED_v0",
        "scalar_scope_backflow_status: NO_BACKFLOW_DETECTED_v0",
        "hold_refine_condition_status: NOT_HIT_v0",
        "momentum_extension_rejection_status: ENFORCED_v0",
        "decision_outcome: AUTHORIZE_PACKET21_BOUNDED_TARGET_v0",
        "packet21_physics_quantity_tightened:",
        "packet21_discriminator_strengthening_requirement:",
        "packet21_ambiguity_reduction_requirement:",
        "packet21_non_repetition_clause:",
        "TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_STATUS_v0: AUTHORIZED_WITH_SINGLE_BOUNDED_TARGET_v0",
        "TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_GATE_v0: REQUIRED_PACKET21_AUTHORIZATION_SCHEMA_AND_AUTHORITY_PARITY",
        "TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_ARTIFACT_v0: toe_qft_gr_seam_packet21_authorization_checkpoint_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet21 authorization doc missing marker: {marker}"


def test_qft_gr_seam_packet21_authorization_checkpoint_schema_and_preconditions() -> None:
    artifact = _read_json(AUTH_CHECKPOINT_PATH)
    assessment_artifact = _read_json(ASSESSMENT_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet21_authorization_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_1AF_QFT_GR_SEAM_PACKET21_AUTHORIZATION"
    assert artifact.get("status") == "PACKET21_AUTHORIZATION_EXPLICIT_DECISION_COMPLETE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("authorization_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_v0.md"
    assert payload.get("parent_assessment_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET20_ASSESSMENT_v0.md"
    assert payload.get("parent_assessment_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_packet20_assessment_checkpoint_v0.json"
    )
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    assessment_decision = assessment_artifact.get("payload", {}).get("packet21_decision", {})
    assert assessment_decision.get("authorized") is True
    assert assessment_decision.get("verdict") == "JUSTIFIED_CONDITIONAL_ON_SINGLE_BOUNDED_TARGET_v0"

    pre = payload.get("preconditions_from_packet20_assessment", {})
    assert pre.get("material_advancement_on_active_question") == "SATISFIED_v0"
    assert pre.get("remaining_target_is_narrower_than_objective") == "SATISFIED_v0"
    assert pre.get("scalar_scope_backflow_status") == "NO_BACKFLOW_DETECTED_v0"
    assert pre.get("hold_refine_condition_status") == "NOT_HIT_v0"
    assert pre.get("momentum_extension_rejection_status") == "ENFORCED_v0"

    decision = payload.get("authorization_decision", {})
    assert decision.get("authorized") is True
    assert decision.get("decision_outcome") == "AUTHORIZE_PACKET21_BOUNDED_TARGET_v0"
    assert decision.get("status") == "AUTHORIZED_WITH_SINGLE_BOUNDED_TARGET_v0"

    bounded = payload.get("packet21_bounded_target", {})
    assert bounded.get("exact_target") == (
        "freeze_one_bounded_handoff_post_completion_closure_finalization_discriminator_that_maps_packet20_closure_completion_witness_to_a_single_non_scalar_expanding_closure_finalization_witness"
    )
    assert bounded.get("discriminator_strengthening_requirement") == (
        "criterion_level_post_completion_closure_finalization_discrimination_beyond_packet20_closure_completion_witness_qualification_required"
    )
    assert bounded.get("ambiguity_reduction_requirement") == (
        "packet21_valid_only_if_residual_interface_ambiguity_reduced_via_new_closure_finalization_discriminative_content"
    )
    assert bounded.get("non_repetition_clause") == (
        "packet21_invalid_if_only_packet20_closure_completion_witness_reencoded_without_new_closure_finalization_discriminative_content"
    )


def test_qft_gr_seam_packet21_authorization_chain_consistency_and_authority_parity() -> None:
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
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_v0.md",
        "formal/output/toe_qft_gr_seam_packet21_authorization_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet21_authorization_gate.py",
    ]
    for ref in refs:
        assert (ref in state_text) or (ref in inventory_text) or (ref in roadmap_text), (
            f"Missing packet21 authorization pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet21 authorization pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_auth = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_STATUS_v0",
    )
    roadmap_auth = _extract_token_from_surfaces([roadmap_text], "TOE_QFT_GR_SEAM_PACKET21_AUTHORIZATION_STATUS_v0")
    assert state_auth == roadmap_auth == "AUTHORIZED_WITH_SINGLE_BOUNDED_TARGET_v0"

    state_seam = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0",
    )
    roadmap_seam = _extract_token_from_surfaces([roadmap_text], "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"
