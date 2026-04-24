from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
THRESHOLD_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md"
THRESHOLD_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet45_reconsideration_numeric_thresholds_checkpoint_v0.json"
CONVERGENCE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
HOLD_FORK_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet45_hold_fork_decision_checkpoint_v0.json"
RETROSPECTIVE_AUDIT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0.json"
MEASUREMENT_PROTOCOL_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet45_numeric_threshold_measurement_protocol_checkpoint_v0.json"
SCORECARD_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet45_reconsideration_scorecard_worksheet_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PACKET45_AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET45_AUTHORIZATION_v0.md"
PACKET45_AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet45_authorization_checkpoint_v0.json"


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


def test_packet45_reconsideration_numeric_thresholds_document_structure() -> None:
    text = _read(THRESHOLD_DOC_PATH)
    required_markers = [
        "Threshold Set ID:",
        "Parent convergence criterion:",
        "Parent packet45 hold/fork decision:",
        "Parent numeric-threshold measurement protocol:",
        "Parent reconsideration scorecard worksheet:",
        "## Numeric Reconsideration Thresholds",
        "NUMERIC_THRESHOLD_MIN_SEAM_GAP_SHRINKAGE_GE_0P12_v0",
        "NUMERIC_THRESHOLD_MIN_MARGINAL_GAIN_INDEX_GE_0P18_v0",
        "NUMERIC_THRESHOLD_MAX_STAGNATION_STREAK_LE_1_OF_3_v0",
        "NUMERIC_THRESHOLD_PACKET45_RELEASE_REQUIRES_ALL_NUMERIC_AND_EXISTING_BINDINGS_v0",
        "TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0",
        "TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Numeric-threshold doc missing marker: {marker}"


def test_packet45_reconsideration_numeric_thresholds_checkpoint_schema_and_alignment() -> None:
    artifact = _read_json(THRESHOLD_CHECKPOINT_PATH)
    convergence = _read_json(CONVERGENCE_CHECKPOINT_PATH)
    hold_fork = _read_json(HOLD_FORK_CHECKPOINT_PATH)
    retrospective = _read_json(RETROSPECTIVE_AUDIT_CHECKPOINT_PATH)
    protocol = _read_json(MEASUREMENT_PROTOCOL_CHECKPOINT_PATH)
    scorecard = _read_json(SCORECARD_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet45_reconsideration_numeric_thresholds_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2Y_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS"
    assert artifact.get("status") == "PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_ACTIVE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("threshold_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"
    assert payload.get("baseline_window_packets") == "packet39_to_packet40"
    assert payload.get("parent_measurement_protocol_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md"
    assert payload.get("parent_measurement_protocol_checkpoint_path") == "formal/output/toe_qft_gr_seam_packet45_numeric_threshold_measurement_protocol_checkpoint_v0.json"
    assert payload.get("parent_scorecard_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md"
    assert payload.get("parent_scorecard_checkpoint_path") == "formal/output/toe_qft_gr_seam_packet45_reconsideration_scorecard_worksheet_checkpoint_v0.json"

    thresholds = payload.get("numeric_thresholds", {})
    assert thresholds.get("min_seam_gap_shrinkage_fraction", {}).get("required_minimum") == 0.12
    assert thresholds.get("min_marginal_gain_index", {}).get("required_minimum") == 0.18
    assert thresholds.get("max_consecutive_stagnant_packets", {}).get("required_maximum") == 1
    assert thresholds.get("max_consecutive_stagnant_packets", {}).get("window_size") == 3
    assert thresholds.get("packet45_reconsideration_release_gate", {}).get("all_numeric_thresholds_required") is True
    assert thresholds.get("packet45_reconsideration_release_gate", {}).get("existing_review_layers_required") is True

    measurement = payload.get("measurement_discipline", {})
    assert measurement.get("measurement_protocol_binding_status") == "REQUIRED_v0"
    assert measurement.get("reconsideration_scorecard_binding_status") == "REQUIRED_v0"

    assert convergence.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"
    assert hold_fork.get("status") == "PACKET45_HOLD_FORK_DECISION_COMPLETE_HOLD_v0"
    assert retrospective.get("status") == "RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_COMPLETE_v0"
    assert protocol.get("status") == "PACKET45_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_ACTIVE_v0"
    assert scorecard.get("status") == "PACKET45_RECONSIDERATION_SCORECARD_WORKSHEET_ACTIVE_v0"


def test_packet45_reconsideration_numeric_thresholds_authority_parity_and_freeze() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md",
        "formal/output/toe_qft_gr_seam_packet45_reconsideration_numeric_thresholds_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet45_reconsideration_numeric_thresholds_gate.py",
    ]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing numeric-threshold pointer in compact-State or central inventory: {ref}"
        )
        assert ref in roadmap_text, f"Missing numeric-threshold pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0"
    )
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0")
    assert state_status == roadmap_status == "ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0"

    state_outcome = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0"
    )
    roadmap_outcome = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0")
    assert state_outcome == roadmap_outcome == "HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0"

    assert not PACKET45_AUTH_DOC_PATH.exists(), "Packet45 authorization doc must not exist under numeric-threshold hold"
    assert not PACKET45_AUTH_CHECKPOINT_PATH.exists(), "Packet45 authorization checkpoint must not exist under numeric-threshold hold"



