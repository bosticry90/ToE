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
PROTOCOL_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md"
PROTOCOL_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet50_numeric_threshold_measurement_protocol_checkpoint_v0.json"
SCORECARD_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet50_reconsideration_scorecard_worksheet_checkpoint_v0.json"
NUMERIC_THRESHOLDS_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet50_reconsideration_numeric_thresholds_checkpoint_v0.json"
CONVERGENCE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
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


def test_packet50_numeric_threshold_measurement_protocol_document_structure() -> None:
    text = _read(PROTOCOL_DOC_PATH)
    required_markers = [
        "Protocol ID:",
        "Parent packet50 reconsideration numeric thresholds:",
        "Parent packet50 reconsideration scorecard worksheet:",
        "## Threshold 1 Computation: Seam-Gap Shrinkage Fraction",
        "G(c) = 0.5D(c) + 0.3A(c) + 0.2O(c)",
        "S(c) =",
        "M(c) = 0.5N(c) + 0.3",
        "Streak3(c)",
        "## Admissible Evidence Surfaces",
        "TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0",
        "TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Measurement protocol doc missing marker: {marker}"


def test_packet50_numeric_threshold_measurement_protocol_checkpoint_schema_and_alignment() -> None:
    artifact = _read_json(PROTOCOL_CHECKPOINT_PATH)
    scorecard = _read_json(SCORECARD_CHECKPOINT_PATH)
    thresholds = _read_json(NUMERIC_THRESHOLDS_CHECKPOINT_PATH)
    convergence = _read_json(CONVERGENCE_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet50_numeric_threshold_measurement_protocol_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2Z_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL"
    assert artifact.get("status") == "PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_ACTIVE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("protocol_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md"
    assert payload.get("parent_scorecard_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md"
    assert payload.get("parent_scorecard_checkpoint_path") == "formal/output/toe_qft_gr_seam_packet50_reconsideration_scorecard_worksheet_checkpoint_v0.json"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    formulas = payload.get("formulas", {})
    assert "G(c)=0.5*D(c)+0.3*A(c)+0.2*O(c)" == formulas.get("gap_score")
    assert "S(c)=max(0,(G(c-1)-G(c))/max(G(c-1),eps))" == formulas.get("seam_gap_shrinkage_fraction")
    assert "M(c)=0.5*N(c)+0.3*max(0,A(c-1)-A(c))+0.2*max(0,O(c-1)-O(c))" == formulas.get("marginal_gain_index")

    rules = payload.get("threshold_pass_rules", {})
    assert rules.get("threshold_1") == "S(c)>=0.12"
    assert rules.get("threshold_2") == "M(c)>=0.18"
    assert rules.get("threshold_3") == "Streak3(c)<=1"

    admissible = payload.get("admissible_evidence_surfaces", [])
    assert "formal/output/toe_qft_gr_seam_packet*_assessment_checkpoint_v0.json" in admissible
    assert "formal/output/toe_qft_gr_seam_packet50_reconsideration_numeric_thresholds_checkpoint_v0.json" in admissible
    assert "formal/output/toe_qft_gr_seam_packet50_reconsideration_scorecard_worksheet_checkpoint_v0.json" in admissible

    scorecard_binding = payload.get("scorecard_binding", {})
    assert scorecard_binding.get("scorecard_required") is True
    assert scorecard_binding.get("scorecard_schema_status") == "REQUIRED_CANONICAL_WORKSHEET_v0"

    assert scorecard.get("status") == "PACKET50_RECONSIDERATION_SCORECARD_WORKSHEET_ACTIVE_v0"
    assert thresholds.get("status") == "PACKET50_RECONSIDERATION_NUMERIC_THRESHOLDS_ACTIVE_v0"
    assert convergence.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"


def test_packet50_numeric_threshold_measurement_protocol_authority_parity_and_freeze() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md",
        "formal/output/toe_qft_gr_seam_packet50_numeric_threshold_measurement_protocol_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet50_numeric_threshold_measurement_protocol_gate.py",
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md",
        "formal/output/toe_qft_gr_seam_packet50_reconsideration_scorecard_worksheet_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet50_reconsideration_scorecard_worksheet_gate.py",
    ]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing measurement protocol pointer in compact-State or central inventory: {ref}"
        )
        assert ref in roadmap_text, f"Missing measurement protocol pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0"
    )
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0")
    assert state_status == roadmap_status == "ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0"

    state_outcome = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0"
    )
    roadmap_outcome = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0")
    assert state_outcome == roadmap_outcome == "HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0"

    assert not PACKET50_AUTH_DOC_PATH.exists(), "Packet49 authorization doc must not exist under measurement-protocol hold"
    assert not PACKET50_AUTH_CHECKPOINT_PATH.exists(), "Packet49 authorization checkpoint must not exist under measurement-protocol hold"







