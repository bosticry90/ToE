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
DECISION_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_v0.md"
DECISION_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet53_hold_fork_decision_checkpoint_v0.json"
ELIGIBILITY_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET53_ELIGIBILITY_REVIEW_v0.md"
ELIGIBILITY_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet53_eligibility_review_checkpoint_v0.json"
TARGETED_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET53_TARGETED_JUSTIFICATION_REVIEW_v0.md"
TARGETED_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet53_targeted_justification_review_checkpoint_v0.json"
CONVERGENCE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PACKET53_AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET53_AUTHORIZATION_v0.md"
PACKET53_AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet53_authorization_checkpoint_v0.json"


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


def test_qft_gr_seam_packet53_hold_fork_decision_document_structure() -> None:
    text = _read(DECISION_DOC_PATH)
    required_markers = [
        "Decision ID:",
        "Parent eligibility review:",
        "Parent targeted justification review:",
        "Parent convergence criterion:",
        "## Decision Branches",
        "disposition_authorize: INACTIVE",
        "disposition_hold: ACTIVE",
        "disposition_fork: INACTIVE",
        "disposition_terminate: INACTIVE",
        "## Decision Rationale",
        "eligibility_review_alignment: REVIEW_COMPLETE_HOLD_v0",
        "targeted_justification_alignment: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0",
        "convergence_alignment: FROZEN_PENDING_CONVERGENCE_BINDING_v0",
        "decision_outcome: HOLD_PACKET53_AUTHORIZATION_v0",
        "packet53_authorization_freeze_status: ENFORCED_v0",
        "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0",
        "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0",
        "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_GATE_v0: REQUIRED_PACKET53_HOLD_FORK_DECISION_SCHEMA_AND_DISPOSITION_ALIGNMENT",
        "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_ARTIFACT_v0: toe_qft_gr_seam_packet53_hold_fork_decision_checkpoint_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet49 hold-fork decision doc missing marker: {marker}"


def test_qft_gr_seam_packet53_hold_fork_decision_checkpoint_schema_and_alignment() -> None:
    artifact = _read_json(DECISION_CHECKPOINT_PATH)
    eligibility_artifact = _read_json(ELIGIBILITY_CHECKPOINT_PATH)
    targeted_artifact = _read_json(TARGETED_CHECKPOINT_PATH)
    convergence_artifact = _read_json(CONVERGENCE_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet53_hold_fork_decision_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2W_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION"
    assert artifact.get("status") == "PACKET53_HOLD_FORK_DECISION_COMPLETE_HOLD_v0"

    payload = artifact.get("payload", {})
    assert payload.get("decision_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_v0.md"
    assert payload.get("parent_eligibility_review_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_ELIGIBILITY_REVIEW_v0.md"
    assert payload.get("parent_targeted_justification_review_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_TARGETED_JUSTIFICATION_REVIEW_v0.md"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    branches = payload.get("decision_branches", {})
    assert branches.get("disposition_authorize") == "INACTIVE"
    assert branches.get("disposition_hold") == "ACTIVE"
    assert branches.get("disposition_fork") == "INACTIVE"
    assert branches.get("disposition_terminate") == "INACTIVE"

    output = payload.get("decision_output", {})
    assert output.get("decision_outcome") == "HOLD_PACKET53_AUTHORIZATION_v0"
    assert output.get("packet53_authorization_freeze_status") == "ENFORCED_v0"

    assert eligibility_artifact.get("status") == "PACKET53_ELIGIBILITY_REVIEW_COMPLETE_HOLD_v0"
    assert targeted_artifact.get("status") == "PACKET53_TARGETED_JUSTIFICATION_REVIEW_COMPLETE_INSUFFICIENT_v0"
    assert convergence_artifact.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"


def test_qft_gr_seam_packet53_hold_fork_decision_authority_parity_and_freeze() -> None:
    decision_text = _read(DECISION_DOC_PATH)
    eligibility_text = _read(ELIGIBILITY_DOC_PATH)
    targeted_text = _read(TARGETED_DOC_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in decision_text
    assert q in eligibility_text
    assert q in targeted_text

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_v0.md",
        "formal/output/toe_qft_gr_seam_packet53_hold_fork_decision_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet53_hold_fork_decision_gate.py",
    ]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing packet53 hold-fork decision pointer in compact-State or central inventory: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet53 hold-fork decision pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_STATUS_v0"
    )
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_STATUS_v0")
    assert state_status == roadmap_status == "DECISION_COMPLETE_HOLD_v0"

    state_outcome = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_OUTCOME_v0"
    )
    roadmap_outcome = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_OUTCOME_v0")
    assert state_outcome == roadmap_outcome == "HOLD_v0"

    assert not PACKET53_AUTH_DOC_PATH.exists(), "Packet49 authorization doc must not exist during hold-fork HOLD disposition"
    assert not PACKET53_AUTH_CHECKPOINT_PATH.exists(), "Packet49 authorization checkpoint must not exist during hold-fork HOLD disposition"








