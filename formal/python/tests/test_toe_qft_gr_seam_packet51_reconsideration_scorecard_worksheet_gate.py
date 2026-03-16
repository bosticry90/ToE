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
SCORECARD_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md"
SCORECARD_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet51_reconsideration_scorecard_worksheet_checkpoint_v0.json"
PROTOCOL_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet51_numeric_threshold_measurement_protocol_checkpoint_v0.json"
THRESHOLDS_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet51_reconsideration_numeric_thresholds_checkpoint_v0.json"
CONVERGENCE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PACKET51_AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET51_AUTHORIZATION_v0.md"
PACKET51_AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet51_authorization_checkpoint_v0.json"


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


def test_packet51_reconsideration_scorecard_document_structure() -> None:
    text = _read(SCORECARD_DOC_PATH)
    required_markers = [
        "Worksheet ID:",
        "Parent packet51 numeric-threshold measurement protocol:",
        "## Canonical Inputs",
        "## Canonical Computation Lines",
        "G(c) = 0.5D(c) + 0.3A(c) + 0.2O(c)",
        "S(c) =",
        "M(c) = 0.5N(c) + 0.3",
        "Streak3(c)",
        "## Threshold Pass/Fail Registry",
        "## Admissible Evidence Registry",
        "TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0",
        "TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Scorecard worksheet doc missing marker: {marker}"


def test_packet51_reconsideration_scorecard_checkpoint_schema_and_alignment() -> None:
    artifact = _read_json(SCORECARD_CHECKPOINT_PATH)
    protocol = _read_json(PROTOCOL_CHECKPOINT_PATH)
    thresholds = _read_json(THRESHOLDS_CHECKPOINT_PATH)
    convergence = _read_json(CONVERGENCE_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet51_reconsideration_scorecard_worksheet_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2ZA_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_WORKSHEET"
    assert artifact.get("status") == "PACKET51_RECONSIDERATION_SCORECARD_WORKSHEET_ACTIVE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("scorecard_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md"
    assert payload.get("parent_measurement_protocol_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md"
    assert payload.get("parent_numeric_thresholds_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    worksheet = payload.get("worksheet_schema", {})
    assert "cycle_id" in worksheet.get("required_inputs", [])
    assert "S_value" in worksheet.get("computed_fields", [])
    assert "threshold_4_pass" in worksheet.get("threshold_pass_fields", [])
    assert worksheet.get("required_evidence_field") == "evidence_sources_used"
    assert worksheet.get("required_disposition_field") == "disposition_recommendation"

    rules = payload.get("threshold_rules", {})
    assert rules.get("threshold_1") == "S(c)>=0.12"
    assert rules.get("threshold_2") == "M(c)>=0.18"
    assert rules.get("threshold_3") == "Streak3(c)<=1"

    disposition = payload.get("disposition_rules", {})
    assert disposition.get("default_disposition_recommendation") == "HOLD_RETAINED_v0"
    assert disposition.get("authorization_artifact_creation") == "FORBIDDEN_v0"

    assert protocol.get("status") == "PACKET51_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_ACTIVE_v0"
    assert thresholds.get("status") == "PACKET51_RECONSIDERATION_NUMERIC_THRESHOLDS_ACTIVE_v0"
    assert convergence.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"


def test_packet51_reconsideration_scorecard_authority_parity_and_freeze() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md",
        "formal/output/toe_qft_gr_seam_packet51_reconsideration_scorecard_worksheet_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet51_reconsideration_scorecard_worksheet_gate.py",
    ]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing scorecard worksheet pointer in compact-State or central inventory: {ref}"
        )
        assert ref in roadmap_text, f"Missing scorecard worksheet pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_STATUS_v0"
    )
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_STATUS_v0")
    assert state_status == roadmap_status == "ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0"

    state_outcome = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_OUTCOME_v0"
    )
    roadmap_outcome = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_OUTCOME_v0")
    assert state_outcome == roadmap_outcome == "HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0"

    assert not PACKET51_AUTH_DOC_PATH.exists(), "Packet49 authorization doc must not exist under scorecard-governed hold"
    assert not PACKET51_AUTH_CHECKPOINT_PATH.exists(), "Packet49 authorization checkpoint must not exist under scorecard-governed hold"







