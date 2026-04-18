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
RECORD_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_DECISION_RECORD_v0.md"
CLOSEOUT_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_closeout_20260417_v0.json"
REFINEMENT_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_master_action_computational_analysis_packet_01_refinement_01_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-.:/]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_toe_master_action_computational_analysis_packet_01_refinement_closeout_decision_record_gate() -> None:
    record_text = _read(RECORD_DOC_PATH)
    closeout_report = json.loads(_read(CLOSEOUT_REPORT_PATH))
    refinement_artifact = json.loads(_read(REFINEMENT_ARTIFACT_PATH))
    summary = closeout_report.get("summary", {})
    criteria = closeout_report.get("criteria", {})
    payload = refinement_artifact.get("payload", {})

    assert _extract_token(record_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(record_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_RESULT_v0") == "RETAIN_REFINEMENT_v0"
    assert _extract_token(record_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_BASIS_v0") == "PERTURBATION_WINDOW_TIGHTENING_REDUCED_REGIME_SPAN_WITHOUT_BREAKING_SIGNAL"

    assert summary.get("decision") == "RETAIN_REFINEMENT_v0"
    assert summary.get("packet01_family_closed") is True
    assert summary.get("authorized_follow_on") == "NONE"
    assert criteria.get("packet02_authorized") is False
    assert criteria.get("gpu_backend_authorized") is False
    assert criteria.get("lane_reopen_implication") is False
    assert criteria.get("blocker_movement_claim") is False
    assert payload.get("packet02_authorized") is False
    assert payload.get("gpu_backend_authorized") is False
    assert payload.get("lane_reopen_implication") is False
    assert payload.get("blocker_movement_claim") is False

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_DECISION_RECORD_v0.md",
        "formal/output/reports/toe_master_action_computational_analysis_packet_01_refinement_closeout_20260417_v0.json",
        "formal/python/tests/test_toe_master_action_computational_analysis_packet_01_refinement_closeout_decision_record_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text

