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
AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_v0.md"
AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet07_authorization_checkpoint_v0.json"
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_v0.md"
ASSESSMENT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet06_assessment_checkpoint_v0.json"
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


def test_qft_gr_seam_packet07_authorization_document_structure() -> None:
    text = _read(AUTH_DOC_PATH)
    required_markers = [
        "Authorization ID:",
        "Parent assessment:",
        "Parent objective:",
        "## Decision Branches",
        "branch_a_authorize_packet07: ACTIVE",
        "branch_b_hold_and_refine_objective: INACTIVE",
        "## Explicit Decision",
        "decision_outcome: AUTHORIZE_PACKET07_BOUNDED_TARGET_v0",
        "TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_STATUS_v0: AUTHORIZED_WITH_EXACT_BOUNDED_TARGET_v0",
        "TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_GATE_v0: REQUIRED_PACKET07_AUTHORIZATION_SCHEMA_AND_AUTHORITY_PARITY",
        "TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_ARTIFACT_v0: toe_qft_gr_seam_packet07_authorization_checkpoint_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet07 authorization doc missing marker: {marker}"


def test_qft_gr_seam_packet07_authorization_checkpoint_schema() -> None:
    artifact = _read_json(AUTH_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet07_authorization_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_1B_QFT_GR_SEAM_PACKET07_AUTHORIZATION"
    assert artifact.get("status") == "PACKET07_AUTHORIZATION_EXPLICIT_DECISION_COMPLETE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("authorization_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_v0.md"
    assert payload.get("parent_assessment_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_v0.md"
    assert payload.get("parent_assessment_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_packet06_assessment_checkpoint_v0.json"
    )
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    decision = payload.get("authorization_decision", {})
    assert decision.get("authorized") is True
    assert decision.get("decision_outcome") == "AUTHORIZE_PACKET07_BOUNDED_TARGET_v0"
    assert decision.get("status") == "AUTHORIZED_WITH_EXACT_BOUNDED_TARGET_v0"
    assert decision.get("branch_a_authorize_packet07") == "ACTIVE"
    assert decision.get("branch_b_hold_and_refine_objective") == "INACTIVE"

    bounded = payload.get("packet07_bounded_target", {})
    assert bounded.get("exact_target") == "freeze_assumption_to_gr_interface_consistency_delta_map_without_scalar_scope_expansion"


def test_qft_gr_seam_packet07_authorization_parent_consistency_and_authority_parity() -> None:
    auth_text = _read(AUTH_DOC_PATH)
    assessment_text = _read(ASSESSMENT_DOC_PATH)
    objective_text = _read(OBJECTIVE_DOC_PATH)
    auth_checkpoint = _read_json(AUTH_CHECKPOINT_PATH)
    assessment_checkpoint = _read_json(ASSESSMENT_CHECKPOINT_PATH)
    objective_checkpoint = _read_json(OBJECTIVE_CHECKPOINT_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in auth_text
    assert q in assessment_text
    assert q in objective_text
    assert auth_checkpoint["payload"].get("active_seam_question") == q
    assert assessment_checkpoint["payload"].get("active_seam_question") == q
    assert objective_checkpoint["payload"].get("active_seam_question") == q

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_v0.md",
        "formal/output/toe_qft_gr_seam_packet07_authorization_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet07_authorization_gate.py",
    ]
    for ref in refs:
        assert (ref in state_text) or (ref in inventory_text) or (ref in roadmap_text), (
            f"Missing packet07 authorization pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet07 authorization pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_auth = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_STATUS_v0",
    )
    roadmap_auth = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET07_AUTHORIZATION_STATUS_v0")
    assert state_auth == roadmap_auth == "AUTHORIZED_WITH_EXACT_BOUNDED_TARGET_v0"

    state_seam = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0",
    )
    roadmap_seam = _extract_token(roadmap_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"