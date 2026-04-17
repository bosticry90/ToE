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
RECORD_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_RECORD_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_v0.json"
DECISION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_computational_analysis_packet_01_decision_20260416_v0.json"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-./]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qm_stat_rl10_computational_analysis_packet_01_decision_record_gate() -> None:
    record_text = _read(RECORD_DOC_PATH)
    packet = json.loads(_read(ARTIFACT_PATH))
    decision_report = json.loads(_read(DECISION_REPORT_PATH))
    payload = packet.get("payload", {})
    criteria = decision_report.get("criteria", {})
    summary = decision_report.get("summary", {})

    assert _extract_token(record_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_RECORD_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(record_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_RESULT_v0") == "REFINE_v0"
    assert _extract_token(record_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_BASIS_v0") == "SIGNAL_IS_MEANINGFUL_BUT_PACKET01_BOUNDARY_REMAINS_INCONCLUSIVE"
    assert _extract_token(record_text, "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_GUARD_v0") == "NO_PACKET02_NO_RESTART_NO_BLOCKER_MOVEMENT"

    assert payload.get("decision") == "INCONCLUSIVE_v0"
    assert payload.get("decision_record_pointer") == (
        "formal/docs/paper/DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_RECORD_v0.md"
    )

    assert summary.get("decision") == "REFINE_v0"
    assert summary.get("packet_level_decision_remains") == "INCONCLUSIVE_v0"
    assert criteria.get("packet02_authorized") is False
    assert criteria.get("restart_implication") is False
    assert criteria.get("blocker_movement_claim") is False
    assert summary.get("authorized_follow_on") == "ONE_BOUNDED_PACKET01_REFINEMENT_ONLY"

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_RECORD_v0.md",
        "formal/python/tests/test_qm_stat_rl10_computational_analysis_packet_01_decision_record_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text