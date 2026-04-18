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
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_PRESERVATION_NOTE_v0.md"
CLOSEOUT_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_closeout_20260417_v0.json"
REFINEMENT_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-.:/]+)", text)
    assert match is not None, f"Missing token `{token_name}`."
    return match.group(1)


def test_toe_master_action_computational_analysis_packet_01_family_preservation_note_gate() -> None:
    note_text = _read(NOTE_PATH)
    closeout_report = json.loads(_read(CLOSEOUT_REPORT_PATH))
    refinement_report = json.loads(_read(REFINEMENT_REPORT_PATH))
    closeout_summary = closeout_report.get("summary", {})

    assert _extract_token(note_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_STATUS_v0") == "PRESERVED_CLOSED_SUCCESS_WITHOUT_ESCALATION"
    assert _extract_token(note_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_OUTCOME_v0") == "RETAIN_REFINEMENT_v0"
    assert _extract_token(note_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_CANONICAL_ENDPOINT_v0") == "formal/output/reports/toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json"

    assert closeout_summary.get("decision") == "RETAIN_REFINEMENT_v0"
    assert closeout_summary.get("authorized_follow_on") == "NONE"
    assert closeout_summary.get("packet01_family_closed") is True
    assert refinement_report.get("summary", {}).get("packet_decision") == "INCONCLUSIVE_v0"

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    for ref in (
        "formal/docs/paper/TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_PRESERVATION_NOTE_v0.md",
        "formal/python/tests/test_toe_master_action_computational_analysis_packet_01_family_preservation_note_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text
