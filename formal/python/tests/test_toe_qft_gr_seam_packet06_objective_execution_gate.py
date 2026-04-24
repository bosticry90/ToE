from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
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


def test_qft_gr_seam_packet06_document_structure() -> None:
    text = _read(PACKET_DOC_PATH)
    required_markers = [
        "Packet ID:",
        "Parent objective:",
        "## Technical Deliverable",
        "## Objective Advancement Verdict",
        "## Scalar Freeze Compliance",
        "## Seam Guardrails",
        "TOE_QFT_GR_SEAM_PACKET06_STATUS_v0: EXECUTED_BOUNDED_OBJECTIVE_STEP_v0",
        "TOE_QFT_GR_SEAM_PACKET06_OBJECTIVE_ALIGNMENT_v0: DIRECT_ADVANCEMENT_CONFIRMED_v0",
        "TOE_QFT_GR_SEAM_PACKET06_GATE_v0: REQUIRED_PACKET06_SCHEMA_AND_OBJECTIVE_ALIGNMENT",
        "TOE_QFT_GR_SEAM_PACKET06_ARTIFACT_v0: toe_qft_gr_seam_packet06_objective_execution_checkpoint_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet06 objective execution doc missing marker: {marker}"


def test_qft_gr_seam_packet06_checkpoint_schema_and_objective_alignment() -> None:
    artifact = _read_json(PACKET_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet06_objective_execution_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_1_QFT_GR_SEAM_PACKET06_OBJECTIVE_EXECUTION"
    assert artifact.get("status") == "PACKET06_EXECUTED_UNDER_OBJECTIVE_LOCK_v0"

    payload = artifact.get("payload", {})
    assert payload.get("packet_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET06_OBJECTIVE_EXECUTION_v0.md"
    assert payload.get("parent_objective_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
    assert payload.get("parent_objective_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json"
    )

    advancement = payload.get("objective_advancement", {})
    assert advancement.get("advanced") is True
    assert advancement.get("verdict") == "ADVANCED_BY_PACKET06_v0"

    guardrails = payload.get("guardrails", {})
    assert guardrails.get("seam_fork_decision_status") == "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"
    assert guardrails.get("execution_scope") == "SINGLE_PACKET_SINGLE_OBJECTIVE_STEP_v0"


def test_qft_gr_seam_packet06_parent_objective_consistency_and_authority_parity() -> None:
    packet_text = _read(PACKET_DOC_PATH)
    objective_text = _read(OBJECTIVE_DOC_PATH)
    objective_checkpoint = _read_json(OBJECTIVE_CHECKPOINT_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    assert "stress_energy_to_weak_curvature_handoff_strengthening" in packet_text
    assert "stress_energy_to_weak_curvature_handoff_strengthening" in objective_text
    assert (
        objective_checkpoint["payload"].get("active_seam_question")
        == "stress_energy_to_weak_curvature_handoff_strengthening"
    )

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET06_OBJECTIVE_EXECUTION_v0.md",
        "formal/output/toe_qft_gr_seam_packet06_objective_execution_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet06_objective_execution_gate.py",
    ]
    for ref in refs:
        assert (ref in state_text) or (ref in inventory_text) or (ref in roadmap_text), (
            f"Missing packet06 pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet06 pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_seam = _extract_token_from_surfaces(
        [state_text, inventory_text],
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0",
    )
    roadmap_seam = _extract_token(roadmap_text, "QFT_GR_SEAM_FORK_DECISION_STATUS_v0")
    assert state_seam == roadmap_seam == "HOLD_FOR_SCALAR_PUBLICATION_v0"
