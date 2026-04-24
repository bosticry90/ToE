from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_v0.md"
ASSESSMENT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet06_assessment_checkpoint_v0.json"
PACKET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET06_OBJECTIVE_EXECUTION_v0.md"
PACKET_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet06_objective_execution_checkpoint_v0.json"
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


def test_qft_gr_seam_packet06_assessment_document_structure() -> None:
    text = _read(ASSESSMENT_DOC_PATH)
    required_markers = [
        "Assessment ID:",
        "Parent packet:",
        "Parent objective:",
        "## Assessment Questions",
        "1. what packet06 actually strengthened",
        "2. what remained unchanged",
        "3. whether packet06 materially advanced the seam objective",
        "4. whether packet07 is justified, and if so, what exact bounded target it should serve",
        "TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_STATUS_v0: ASSESSED_OBJECTIVE_ADVANCEMENT_VERIFIED_v0",
        "TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_GATE_v0: REQUIRED_PACKET06_ASSESSMENT_SCHEMA_AND_AUTHORITY_PARITY",
        "TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_ARTIFACT_v0: toe_qft_gr_seam_packet06_assessment_checkpoint_v0",
        "material_advancement_verdict: YES_MATERIAL_ADVANCEMENT_v0",
        "packet07_authorization_verdict: JUSTIFIED_CONDITIONAL_ON_BOUNDED_TARGET_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet06 assessment doc missing marker: {marker}"


def test_qft_gr_seam_packet06_assessment_checkpoint_schema() -> None:
    artifact = _read_json(ASSESSMENT_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet06_assessment_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_1A_QFT_GR_SEAM_PACKET06_ASSESSMENT"
    assert artifact.get("status") == "PACKET06_ASSESSMENT_COMPLETE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("assessment_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_v0.md"
    assert payload.get("parent_packet_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET06_OBJECTIVE_EXECUTION_v0.md"
    assert payload.get("parent_packet_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_packet06_objective_execution_checkpoint_v0.json"
    )
    assert payload.get("parent_objective_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
    assert payload.get("parent_objective_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json"
    )
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    summary = payload.get("assessment_summary", {})
    assert summary.get("material_advancement") is True
    assert summary.get("material_advancement_verdict") == "YES_MATERIAL_ADVANCEMENT_v0"

    packet07 = payload.get("packet07_decision", {})
    assert packet07.get("authorized") is True
    assert packet07.get("verdict") == "JUSTIFIED_CONDITIONAL_ON_BOUNDED_TARGET_v0"
    assert packet07.get("exact_bounded_target") == (
        "freeze_assumption_to_gr_interface_consistency_delta_map_without_scalar_scope_expansion"
    )


def test_qft_gr_seam_packet06_assessment_parent_consistency_and_authority_parity() -> None:
    assessment_text = _read(ASSESSMENT_DOC_PATH)
    packet_text = _read(PACKET_DOC_PATH)
    objective_text = _read(OBJECTIVE_DOC_PATH)
    packet_checkpoint = _read_json(PACKET_CHECKPOINT_PATH)
    objective_checkpoint = _read_json(OBJECTIVE_CHECKPOINT_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in assessment_text
    assert q in packet_text
    assert q in objective_text
    assert packet_checkpoint["payload"].get("active_seam_question") == q
    assert objective_checkpoint["payload"].get("active_seam_question") == q

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_v0.md",
        "formal/output/toe_qft_gr_seam_packet06_assessment_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet06_assessment_gate.py",
    ]
    for ref in refs:
        assert (ref in state_text) or (ref in inventory_text) or (ref in roadmap_text), (
            f"Missing packet06 assessment pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet06 assessment pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_assessment = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_STATUS_v0",
    )
    roadmap_assessment = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET06_ASSESSMENT_STATUS_v0")
    assert state_assessment == roadmap_assessment == "ASSESSED_OBJECTIVE_ADVANCEMENT_VERIFIED_v0"

    state_seam = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0",
    )
    roadmap_seam = _extract_token(roadmap_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"