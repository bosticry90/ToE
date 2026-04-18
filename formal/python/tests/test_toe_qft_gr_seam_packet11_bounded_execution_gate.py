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
PACKET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET11_BOUNDED_EXECUTION_v0.md"
PACKET_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet11_bounded_execution_checkpoint_v0.json"
AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET11_AUTHORIZATION_v0.md"
AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet11_authorization_checkpoint_v0.json"
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET10_ASSESSMENT_v0.md"
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


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_surfaces(texts: list[str], token_name: str) -> str:
    for text in texts:
        m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
        if m is not None:
            return m.group(1)
    raise AssertionError(f"Missing token `{token_name}` across authority surfaces.")


def test_qft_gr_seam_packet11_bounded_execution_document_structure() -> None:
    text = _read(PACKET_DOC_PATH)
    required_markers = [
        "Packet ID:",
        "Parent authorization:",
        "Parent objective:",
        "## Authorized Target Binding",
        "authorization_decision_outcome: AUTHORIZE_PACKET11_BOUNDED_TARGET_v0",
        "authorized_exact_target: freeze_one_bounded_handoff_closure_readiness_discriminator_that_maps_packet10_adequacy_witness_to_a_single_non_scalar_expanding_readiness_state",
        "execution_target_match: EXACT_MATCH_CONFIRMED_v0",
        "## Physics Delta (explicit tightening)",
        "readiness_state_token: HANDOFF_CLOSURE_READINESS_STATE_MET_v0",
        "Acceptance criteria (must all pass):",
        "AC1_input_state_binding_to_packet10_adequacy_witness: PASS_v0",
        "AC2_discriminator_rule_explicitness: PASS_v0",
        "AC3_readiness_state_token_pinned: PASS_v0",
        "AC4_no_scalar_scope_expansion_or_backflow: PASS_v0",
        "AC5_non_claim_boundary_preserved: PASS_v0",
        "fallback_hold_triggered: NO_v0",
        "TOE_QFT_GR_SEAM_PACKET11_STATUS_v0: EXECUTED_BOUNDED_TARGET_STEP_v0",
        "TOE_QFT_GR_SEAM_PACKET11_TARGET_ALIGNMENT_v0: AUTHORIZED_TARGET_MATCH_CONFIRMED_v0",
        "TOE_QFT_GR_SEAM_PACKET11_GATE_v0: REQUIRED_PACKET11_EXECUTION_SCHEMA_AND_AUTHORIZATION_ALIGNMENT",
        "TOE_QFT_GR_SEAM_PACKET11_ARTIFACT_v0: toe_qft_gr_seam_packet11_bounded_execution_checkpoint_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet11 execution doc missing marker: {marker}"


def test_qft_gr_seam_packet11_bounded_execution_checkpoint_schema_and_alignment() -> None:
    artifact = _read_json(PACKET_CHECKPOINT_PATH)
    auth_artifact = _read_json(AUTH_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet11_bounded_execution_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_1O_QFT_GR_SEAM_PACKET11_BOUNDED_EXECUTION"
    assert artifact.get("status") == "PACKET11_EXECUTED_UNDER_AUTHORIZED_BOUNDED_TARGET_v0"

    payload = artifact.get("payload", {})
    assert payload.get("packet_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET11_BOUNDED_EXECUTION_v0.md"
    assert payload.get("parent_authorization_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET11_AUTHORIZATION_v0.md"
    assert payload.get("parent_authorization_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_packet11_authorization_checkpoint_v0.json"
    )
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    auth_payload = auth_artifact.get("payload", {})
    assert auth_payload.get("authorization_decision", {}).get("authorized") is True
    assert auth_payload.get("authorization_decision", {}).get("decision_outcome") == "AUTHORIZE_PACKET11_BOUNDED_TARGET_v0"

    binding = payload.get("authorized_target_binding", {})
    assert binding.get("authorization_decision_outcome") == "AUTHORIZE_PACKET11_BOUNDED_TARGET_v0"
    assert binding.get("authorized_exact_target") == (
        "freeze_one_bounded_handoff_closure_readiness_discriminator_that_maps_packet10_adequacy_witness_to_a_single_non_scalar_expanding_readiness_state"
    )
    assert binding.get("authorized_exact_target") == auth_payload.get("packet11_bounded_target", {}).get("exact_target")
    assert binding.get("execution_target_match") == "EXACT_MATCH_CONFIRMED_v0"

    discr = payload.get("closure_readiness_discriminator", {})
    assert discr.get("readiness_state_token") == "HANDOFF_CLOSURE_READINESS_STATE_MET_v0"

    ac = payload.get("acceptance_criteria", {})
    assert ac.get("ac1_input_state_binding_to_packet10_adequacy_witness") == "PASS_v0"
    assert ac.get("ac2_discriminator_rule_explicitness") == "PASS_v0"
    assert ac.get("ac3_readiness_state_token_pinned") == "PASS_v0"
    assert ac.get("ac4_no_scalar_scope_expansion_or_backflow") == "PASS_v0"
    assert ac.get("ac5_non_claim_boundary_preserved") == "PASS_v0"

    fallback = payload.get("fallback_condition", {})
    assert fallback.get("fallback_hold_triggered") == "NO_v0"


def test_qft_gr_seam_packet11_bounded_execution_authority_parity_and_invariance() -> None:
    packet_text = _read(PACKET_DOC_PATH)
    auth_text = _read(AUTH_DOC_PATH)
    assessment_text = _read(ASSESSMENT_DOC_PATH)
    objective_text = _read(OBJECTIVE_DOC_PATH)
    objective_checkpoint = _read_json(OBJECTIVE_CHECKPOINT_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in packet_text
    assert q in auth_text
    assert q in assessment_text
    assert q in objective_text
    assert objective_checkpoint["payload"].get("active_seam_question") == q

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET11_BOUNDED_EXECUTION_v0.md",
        "formal/output/toe_qft_gr_seam_packet11_bounded_execution_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet11_bounded_execution_gate.py",
    ]
    for ref in refs:
        assert (ref in state_text) or (ref in inventory_text) or (ref in roadmap_text), (
            f"Missing packet11 execution pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet11 execution pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_packet11 = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_PACKET11_STATUS_v0",
    )
    roadmap_packet11 = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET11_STATUS_v0")
    assert state_packet11 == roadmap_packet11 == "EXECUTED_BOUNDED_TARGET_STEP_v0"

    state_seam = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0",
    )
    roadmap_seam = _extract_token(roadmap_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"
