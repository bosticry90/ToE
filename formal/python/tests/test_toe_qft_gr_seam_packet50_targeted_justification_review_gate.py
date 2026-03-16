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
REVIEW_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_REVIEW_v0.md"
REVIEW_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet50_targeted_justification_review_checkpoint_v0.json"
ELIGIBILITY_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET50_ELIGIBILITY_REVIEW_v0.md"
ELIGIBILITY_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet50_eligibility_review_checkpoint_v0.json"
CONVERGENCE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
CONVERGENCE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PACKET50_AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET50_AUTHORIZATION_v0.md"
PACKET50_AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet50_authorization_checkpoint_v0.json"


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


def test_qft_gr_seam_packet50_targeted_justification_review_document_structure() -> None:
    text = _read(REVIEW_DOC_PATH)
    required_markers = [
        "Review ID:",
        "Parent eligibility review:",
        "Parent convergence criterion:",
        "## Candidate Packet49 Target Under Review",
        "## Justification Checks",
        "seam_gap_still_measurably_shrinking_check: FAIL_v0_NOT_YET_DEMONSTRATED",
        "expected_marginal_gain_above_threshold_check: FAIL_v0_NOT_YET_DEMONSTRATED",
        "stagnation_clearance_check: FAIL_v0_UNRESOLVED_PENDING_CONCRETE_DISCRIMINATOR_PACKAGE",
        "remaining_gap_narrower_than_objective_check: PASS_v0",
        "## Review Outcome",
        "targeted_justification_verdict: INSUFFICIENT_FOR_PACKET50_AUTHORIZATION_v0",
        "hold_alignment_status: CONSISTENT_WITH_PACKET50_ELIGIBILITY_HOLD_v0",
        "packet50_authorization_freeze_status: ENFORCED_v0",
        "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0",
        "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0",
        "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_GATE_v0: REQUIRED_PACKET50_TARGETED_JUSTIFICATION_SCHEMA_AND_HOLD_ALIGNMENT",
        "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_ARTIFACT_v0: toe_qft_gr_seam_packet50_targeted_justification_review_checkpoint_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet49 targeted justification review doc missing marker: {marker}"


def test_qft_gr_seam_packet50_targeted_justification_review_checkpoint_schema_and_outcome() -> None:
    artifact = _read_json(REVIEW_CHECKPOINT_PATH)
    eligibility_artifact = _read_json(ELIGIBILITY_CHECKPOINT_PATH)
    convergence_artifact = _read_json(CONVERGENCE_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet50_targeted_justification_review_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2V_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_REVIEW"
    assert artifact.get("status") == "PACKET50_TARGETED_JUSTIFICATION_REVIEW_COMPLETE_INSUFFICIENT_v0"

    payload = artifact.get("payload", {})
    assert payload.get("review_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_REVIEW_v0.md"
    assert payload.get("parent_eligibility_review_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_ELIGIBILITY_REVIEW_v0.md"
    assert payload.get("parent_convergence_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    checks = payload.get("justification_checks", {})
    assert checks.get("seam_gap_still_measurably_shrinking_check") == "FAIL_v0_NOT_YET_DEMONSTRATED"
    assert checks.get("expected_marginal_gain_above_threshold_check") == "FAIL_v0_NOT_YET_DEMONSTRATED"
    assert checks.get("stagnation_clearance_check") == "FAIL_v0_UNRESOLVED_PENDING_CONCRETE_DISCRIMINATOR_PACKAGE"
    assert checks.get("remaining_gap_narrower_than_objective_check") == "PASS_v0"

    outcome = payload.get("review_outcome", {})
    assert outcome.get("targeted_justification_verdict") == "INSUFFICIENT_FOR_PACKET50_AUTHORIZATION_v0"
    assert outcome.get("hold_alignment_status") == "CONSISTENT_WITH_PACKET50_ELIGIBILITY_HOLD_v0"

    assert eligibility_artifact.get("status") == "PACKET50_ELIGIBILITY_REVIEW_COMPLETE_HOLD_v0"
    assert convergence_artifact.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"


def test_qft_gr_seam_packet50_targeted_justification_review_authority_parity_and_freeze() -> None:
    review_text = _read(REVIEW_DOC_PATH)
    eligibility_text = _read(ELIGIBILITY_DOC_PATH)
    convergence_text = _read(CONVERGENCE_DOC_PATH)
    assessment_text = _read(ASSESSMENT_DOC_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in review_text
    assert q in eligibility_text
    assert q in convergence_text
    assert q in assessment_text

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_REVIEW_v0.md",
        "formal/output/toe_qft_gr_seam_packet50_targeted_justification_review_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet50_targeted_justification_review_gate.py",
    ]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing packet50 targeted justification pointer in compact-State or central inventory: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet50 targeted justification pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_STATUS_v0"
    )
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_STATUS_v0")
    assert state_status == roadmap_status == "REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0"

    state_outcome = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_OUTCOME_v0"
    )
    roadmap_outcome = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_OUTCOME_v0")
    assert state_outcome == roadmap_outcome == "HOLD_RETAINED_v0"

    assert not PACKET50_AUTH_DOC_PATH.exists(), "Packet49 authorization doc must not exist during targeted-justification hold"
    assert not PACKET50_AUTH_CHECKPOINT_PATH.exists(), "Packet49 authorization checkpoint must not exist during targeted-justification hold"








