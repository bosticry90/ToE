from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "em_u1_micro27_authorization_decision_20260418_v0.json"
)
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "em_u1_micro27_authorization_decision_report.py"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_em_micro27_authorization_report_is_pinned_and_closed() -> None:
    report = json.loads(_read(REPORT_PATH))

    assert report["schema_id"] == "EM_U1_MICRO27_AUTHORIZATION_DECISION_20260418_v0"
    assert report["report_id"] == "EM_U1_MICRO27_AUTHORIZATION_DECISION_REPORT_v0"
    assert report["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert report["criteria"]["micro26_closeout_requires_explicit_authorization"] is True
    assert report["criteria"]["current_progress_classification_is_progress"] is True
    assert report["criteria"]["micro27_target_doc_pinned"] is True
    assert report["criteria"]["em_row_still_live_theorem_gap"] is True
    assert report["criteria"]["distinct_authorization_surface_materialized"] is True

    assert report["summary"]["decision"] == "KEEP_MICRO27_CLOSED_v0"
    assert report["summary"]["decision_basis"] == (
        "GLOBAL_PROGRESS_NONLOCAL_AND_ROW_PILLAR_EM_001_REMAINS_LIVE_THEOREM_GAP"
    )
    assert report["summary"]["authorization_status"] == "NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0"
    assert report["summary"]["automatic_activation_from_global_progress"] is False
    assert report["summary"]["current_progress_classification"] == "PROGRESS"
    assert report["summary"]["em_row_id"] == "ROW-PILLAR-EM-001"
    assert report["summary"]["next_action"] == (
        "OPEN_DISTINCT_MICRO27_AUTHORIZATION_SURFACE_IF_EM_IS_NEXT_BLOCKER_FACING_LANE"
    )
    assert report["summary"]["required_authorization_basis"] == (
        "EM_LOCAL_BLOCKER_EVENT_OR_EXPLICIT_MICRO27_AUTHORIZATION_TRANCHE"
    )

    contradiction = report["target_context"]["live_em_contradiction"]
    assert contradiction["row_id"] == "ROW-PILLAR-EM-001"
    assert contradiction["contradiction_type"] == "PILLAR_M4_COMPLETE_VS_LIVE_THEOREM_GAP"


def test_em_micro27_authorization_tool_and_authority_surfaces_pin_closed_decision() -> None:
    tool_text = _read(TOOL_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    required_tool_tokens = [
        "EM_U1_MICRO27_AUTHORIZATION_DECISION_20260418_v0",
        "EM_U1_MICRO27_AUTHORIZATION_DECISION_REPORT_v0",
        "KEEP_MICRO27_CLOSED_v0",
        "NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0",
        "OPEN_DISTINCT_MICRO27_AUTHORIZATION_SURFACE_IF_EM_IS_NEXT_BLOCKER_FACING_LANE",
        "EM_LOCAL_BLOCKER_EVENT_OR_EXPLICIT_MICRO27_AUTHORIZATION_TRANCHE",
        "ROW-PILLAR-EM-001",
    ]
    missing_tool = [token for token in required_tool_tokens if token not in tool_text]
    assert not missing_tool, "EM Micro-27 authorization tool is missing required token(s): " + ", ".join(missing_tool)

    required_surface_tokens = [
        "formal/python/tools/em_u1_micro27_authorization_decision_report.py",
        "formal/output/reports/em_u1_micro27_authorization_decision_20260418_v0.json",
        "KEEP_MICRO27_CLOSED_v0",
        "NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0",
    ]
    for token in required_surface_tokens:
        assert token in state_text, f"State_of_the_Theory.md missing EM Micro-27 authorization token: {token}"
        assert token in roadmap_text, f"PHYSICS_ROADMAP_v0.md missing EM Micro-27 authorization token: {token}"