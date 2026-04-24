from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
PACKET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_v0.md"
PACKET_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet38_assessment_checkpoint_v0.json"
EXEC_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET38_BOUNDED_EXECUTION_v0.md"
EXEC_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet38_bounded_execution_checkpoint_v0.json"
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


def test_qft_gr_seam_packet38_assessment_document_structure() -> None:
    text = _read(PACKET_DOC_PATH)
    required_markers = [
        "Packet ID:",
        "Parent packet:",
        "## Assessment Inputs",
        "## Bounded Target Satisfaction Verdict",
        "bounded_target_satisfaction_verdict: SATISFIED_v0",
        "## Physics Delta Confirmation",
        "physics_delta_confirmation_status:",
        "CONFIRMED_NON_TRIVIAL_TIGHTENING_v0",
        "## Conditional Packet39 Authorization Projection",
        "freeze_one_bounded_handoff_post_consistency_contradiction_screen_that_maps_packet38_closure_consistency_witness_to_a_single_non_scalar_expanding_closure_contradiction_screen_witness",
        "packet38_bounded_target_satisfaction: SATISFIED_v0",
        "packet38_non_repetition_clause_status: ENFORCED_v0",
        "scalar_scope_backflow_status: NO_BACKFLOW_DETECTED_v0",
        "fallback_hold_triggered: NO_v0",
        "non_claim_boundary_preserved: ENFORCED_v0",
        "readiness_state: CONDITIONAL_READINESS_ONLY_v0",
        "TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_STATUS_v0: BOUNDED_TARGET_CONFIRMED_v0",
        "TOE_QFT_GR_SEAM_PACKET39_AUTHORIZATION_READINESS_v0: CONDITIONAL_READINESS_ONLY_v0",
        "TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_GATE_v0: REQUIRED_PACKET38_ASSESSMENT_SCHEMA_AND_CONDITIONAL_READINESS",
        "TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_ARTIFACT_v0: toe_qft_gr_seam_packet38_assessment_checkpoint_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet38 assessment doc missing marker: {marker}"


def test_qft_gr_seam_packet38_assessment_checkpoint_schema_and_parent_consistency() -> None:
    artifact = _read_json(PACKET_CHECKPOINT_PATH)
    exec_artifact = _read_json(EXEC_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet38_assessment_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2O_QFT_GR_SEAM_PACKET38_ASSESSMENT"
    assert artifact.get("status") == "PACKET38_ASSESSMENT_COMPLETE_CONDITIONAL_PACKET39_READINESS_ONLY_v0"

    payload = artifact.get("payload", {})
    assert payload.get("packet_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_v0.md"
    assert payload.get("parent_packet_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET38_BOUNDED_EXECUTION_v0.md"
    assert payload.get("parent_packet_checkpoint_path") == "formal/output/toe_qft_gr_seam_packet38_bounded_execution_checkpoint_v0.json"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    verdict = payload.get("bounded_target_assessment", {})
    assert verdict.get("execution_target_match") == "EXACT_MATCH_CONFIRMED_v0"
    assert verdict.get("closure_consistency_witness_token_status") == "HANDOFF_CLOSURE_CONSISTENCY_WITNESS_MET_v0"
    assert verdict.get("bounded_target_satisfaction_verdict") == "SATISFIED_v0"

    exec_payload = exec_artifact.get("payload", {})
    exec_ac = exec_payload.get("acceptance_criteria", {})
    assert exec_ac.get("ac1_input_state_binding_to_packet37_closure_coherence_witness") == "PASS_v0"
    assert exec_ac.get("ac2_discriminator_rule_explicitness") == "PASS_v0"
    assert exec_ac.get("ac3_closure_consistency_witness_token_pinned") == "PASS_v0"
    assert exec_ac.get("ac4_non_repetition_clause_enforced") == "PASS_v0"
    assert exec_ac.get("ac5_no_scalar_scope_expansion_or_backflow") == "PASS_v0"
    assert exec_ac.get("ac6_non_claim_boundary_preserved") == "PASS_v0"

    projection = payload.get("packet39_projection", {})
    preconditions = projection.get("authorization_preconditions", {})
    assert preconditions.get("packet38_bounded_target_satisfaction") == "SATISFIED_v0"
    assert preconditions.get("packet38_non_repetition_clause_status") == "ENFORCED_v0"
    assert preconditions.get("scalar_scope_backflow_status") == "NO_BACKFLOW_DETECTED_v0"
    assert preconditions.get("fallback_hold_triggered") == "NO_v0"
    assert preconditions.get("non_claim_boundary_preserved") == "ENFORCED_v0"
    assert projection.get("authorization_readiness", {}).get("readiness_state") == "CONDITIONAL_READINESS_ONLY_v0"


def test_qft_gr_seam_packet38_assessment_authority_parity_and_invariance() -> None:
    packet_text = _read(PACKET_DOC_PATH)
    exec_text = _read(EXEC_DOC_PATH)
    objective_text = _read(OBJECTIVE_DOC_PATH)
    objective_checkpoint = _read_json(OBJECTIVE_CHECKPOINT_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in packet_text
    assert q in exec_text
    assert q in objective_text
    assert objective_checkpoint["payload"].get("active_seam_question") == q

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_v0.md",
        "formal/output/toe_qft_gr_seam_packet38_assessment_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet38_assessment_gate.py",
    ]
    for ref in refs:
        assert any(ref in text for text in (state_text, inventory_text, roadmap_text)), (
            f"Missing packet38 assessment pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet38 assessment pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_assessment = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_STATUS_v0",
    )
    roadmap_assessment = _extract_token_from_surfaces([roadmap_text], "TOE_QFT_GR_SEAM_PACKET38_ASSESSMENT_STATUS_v0")
    assert state_assessment == roadmap_assessment == "BOUNDED_TARGET_CONFIRMED_v0"

    state_readiness = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_PACKET39_AUTHORIZATION_READINESS_v0",
    )
    roadmap_readiness = _extract_token_from_surfaces(
        [roadmap_text],
        "TOE_QFT_GR_SEAM_PACKET39_AUTHORIZATION_READINESS_v0",
    )
    assert state_readiness == roadmap_readiness == "CONDITIONAL_READINESS_ONLY_v0"

    state_seam = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0",
    )
    roadmap_seam = _extract_token_from_surfaces([roadmap_text], "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"
