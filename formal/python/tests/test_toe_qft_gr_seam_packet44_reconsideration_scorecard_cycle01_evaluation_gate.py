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
EVALUATION_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet44_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PACKET44_AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET44_AUTHORIZATION_v0.md"
PACKET44_AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet44_authorization_checkpoint_v0.json"


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


def test_packet44_scorecard_cycle01_checkpoint_schema_and_hold_result() -> None:
    artifact = _read_json(EVALUATION_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet44_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2ZB_QFT_GR_SEAM_PACKET44_RECONSIDERATION_SCORECARD_EVALUATION_CYCLE01"
    assert artifact.get("status") == "PACKET44_RECONSIDERATION_SCORECARD_EVALUATION_CYCLE01_COMPLETE_HOLD_v0"

    payload = artifact.get("payload", {})
    assert payload.get("cycle_id") == "packet44_reconsideration_cycle01_baseline_packet39_to_packet40"
    assert payload.get("formula_version") == "packet44_measurement_protocol_v0"

    availability = payload.get("input_field_availability", {})
    assert all(v is False for v in availability.values())

    thresholds = payload.get("threshold_pass", {})
    assert thresholds.get("threshold_1_pass") is False
    assert thresholds.get("threshold_2_pass") is False
    assert thresholds.get("threshold_3_pass") is False
    assert thresholds.get("threshold_4_pass") is False
    assert thresholds.get("auto_fail_reason") == "MISSING_REQUIRED_NUMERIC_FIELDS_FROM_ADMISSIBLE_CHECKPOINTS_v0"

    assert payload.get("existing_review_layers_pass") is False
    assert payload.get("disposition_recommendation") == "HOLD_RETAINED_v0"
    assert payload.get("authorization_artifact_creation") == "FORBIDDEN_v0"


def test_packet44_scorecard_cycle01_authority_parity_and_freeze() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/output/toe_qft_gr_seam_packet44_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet44_reconsideration_scorecard_cycle01_evaluation_gate.py",
    ]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing scorecard cycle01 pointer in compact-State or central inventory: {ref}"
        )
        assert ref in roadmap_text, f"Missing scorecard cycle01 pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text, inventory_text, "TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0"
    )
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0")
    assert state_status == roadmap_status == "EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0"

    assert not PACKET44_AUTH_DOC_PATH.exists(), "Packet44 authorization doc must not exist after cycle01 scorecard evaluation"
    assert not PACKET44_AUTH_CHECKPOINT_PATH.exists(), "Packet44 authorization checkpoint must not exist after cycle01 scorecard evaluation"


