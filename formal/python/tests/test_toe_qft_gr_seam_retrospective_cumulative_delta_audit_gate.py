from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_v0.md"
AUDIT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0.json"
CONVERGENCE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
HOLD_FORK_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_hold_fork_decision_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PACKET41_AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET41_AUTHORIZATION_v0.md"
PACKET41_AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_authorization_checkpoint_v0.json"


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


def test_qft_gr_seam_retrospective_cumulative_delta_audit_document_structure() -> None:
    text = _read(AUDIT_DOC_PATH)
    required_markers = [
        "Audit ID:",
        "Parent convergence criterion:",
        "Parent packet41 hold/fork decision:",
        "## Cumulative-Delta Findings",
        "cumulative_delta_classification: MATERIALLY_CUMULATIVE_v0",
        "## Plateau and Refinement Findings",
        "marginal_gain_trend: DECELERATING_v0",
        "governance_clean_refinement_share: ELEVATED_v0",
        "stagnation_risk_level: ELEVATED_BUT_NOT_TERMINAL_v0",
        "## Program-Level Classification",
        "program_state_classification: MATERIALLY_CUMULATIVE_WITH_PLATEAU_RISK_v0",
        "packet41_reopen_readiness: NOT_READY_v0",
        "## Disposition Alignment",
        "audit_disposition_outcome: HOLD_RETAINED_EVIDENCE_BASE_UPDATED_v0",
        "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_STATUS_v0: COMPLETE_MATERIAL_CUMULATIVE_WITH_PLATEAU_RISK_v0",
        "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_OUTCOME_v0: HOLD_RETAINED_EVIDENCE_BASE_UPDATED_v0",
        "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_GATE_v0: REQUIRED_RETROSPECTIVE_CUMULATIVE_DELTA_SCHEMA_AND_DISPOSITION_ALIGNMENT",
        "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_ARTIFACT_v0: toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Retrospective cumulative-delta audit doc missing marker: {marker}"


def test_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_schema_and_alignment() -> None:
    artifact = _read_json(AUDIT_CHECKPOINT_PATH)
    convergence = _read_json(CONVERGENCE_CHECKPOINT_PATH)
    hold_fork = _read_json(HOLD_FORK_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2X_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT"
    assert artifact.get("status") == "RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_COMPLETE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("audit_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_v0.md"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    findings = payload.get("cumulative_delta_findings", {})
    assert findings.get("packet39_delta_classification") == "MATERIAL_DISCRIMINATOR_TIGHTENING_v0"
    assert findings.get("packet40_delta_classification") == "MATERIAL_DISCRIMINATOR_TIGHTENING_v0"
    assert findings.get("cumulative_delta_classification") == "MATERIALLY_CUMULATIVE_v0"

    plateau = payload.get("plateau_and_refinement_findings", {})
    assert plateau.get("marginal_gain_trend") == "DECELERATING_v0"
    assert plateau.get("governance_clean_refinement_share") == "ELEVATED_v0"
    assert plateau.get("stagnation_risk_level") == "ELEVATED_BUT_NOT_TERMINAL_v0"

    program = payload.get("program_level_classification", {})
    assert program.get("program_state_classification") == "MATERIALLY_CUMULATIVE_WITH_PLATEAU_RISK_v0"
    assert program.get("packet41_reopen_readiness") == "NOT_READY_v0"

    alignment = payload.get("disposition_alignment", {})
    assert alignment.get("alignment_with_packet41_hold_fork_decision") == "CONSISTENT_DECISION_COMPLETE_HOLD_v0"
    assert alignment.get("audit_disposition_outcome") == "HOLD_RETAINED_EVIDENCE_BASE_UPDATED_v0"

    assert convergence.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"
    assert hold_fork.get("status") == "PACKET41_HOLD_FORK_DECISION_COMPLETE_HOLD_v0"


def test_qft_gr_seam_retrospective_cumulative_delta_audit_authority_parity_and_freeze() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_v0.md",
        "formal/output/toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_retrospective_cumulative_delta_audit_gate.py",
    ]
    for ref in refs:
        assert any(ref in text for text in (state_text, inventory_text, roadmap_text)), (
            f"Missing retrospective audit pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing retrospective audit pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_STATUS_v0",
    )
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_STATUS_v0")
    assert state_status == roadmap_status == "COMPLETE_MATERIAL_CUMULATIVE_WITH_PLATEAU_RISK_v0"

    state_outcome = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text],
        "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_OUTCOME_v0",
    )
    roadmap_outcome = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_OUTCOME_v0")
    assert state_outcome == roadmap_outcome == "HOLD_RETAINED_EVIDENCE_BASE_UPDATED_v0"

    assert not PACKET41_AUTH_DOC_PATH.exists(), "Packet41 authorization doc must not exist during retrospective-audit hold"
    assert not PACKET41_AUTH_CHECKPOINT_PATH.exists(), "Packet41 authorization checkpoint must not exist during retrospective-audit hold"