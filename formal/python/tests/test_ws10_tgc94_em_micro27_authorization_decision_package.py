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
DECISION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "WS_10_TGC_94_EM_MICRO27_AUTHORIZATION_DECISION_PACKAGE_20260418_v0.md"
)
REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "em_u1_micro27_authorization_decision_20260418_v0.json"
)
PLAN_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_THEORY_RESTART_PILOT_PLAN_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_tgc94_decision_package_structure() -> None:
    text = _read(DECISION_PATH)
    required_markers = [
        "# WS-10 TGC-94 EM Micro-27 Authorization Decision Package (2026-04-18)",
        "## Status",
        "- Tranche: TGC-94",
        "## Inputs audited",
        "formal/output/reports/em_u1_micro27_authorization_decision_20260418_v0.json",
        "## Canonical decision tokens",
        "TGC94_EM_MICRO27_DECISION_v0: KEEP_MICRO27_CLOSED_v0",
        "TGC94_EM_MICRO27_AUTHORIZATION_STATUS_v0: NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0",
        "TGC94_EM_MICRO27_PROGRESS_AUTOMATION_v0: GLOBAL_PROGRESS_DOES_NOT_AUTHORIZE_EM_FOLLOW_ON",
        "TGC94_EM_LIVE_ROW_THEOREM_GAP_SIGNAL_v0: ROW_PILLAR_EM_001_REMAINS_LIVE_THEOREM_GAP",
        "## Validation Bundle",
        "formal/python/tests/test_ws10_tgc94_em_micro27_authorization_decision_package.py",
    ]
    missing = [marker for marker in required_markers if marker not in text]
    assert not missing, "TGC-94 decision package missing required marker(s): " + ", ".join(missing)


def test_tgc94_decision_package_matches_live_report() -> None:
    text = _read(DECISION_PATH)
    report = _read_json(REPORT_PATH)
    summary = report.get("summary", {})

    assert summary.get("decision") == "KEEP_MICRO27_CLOSED_v0"
    assert summary.get("authorization_status") == "NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0"
    assert summary.get("required_authorization_basis") == (
        "EM_LOCAL_BLOCKER_EVENT_OR_EXPLICIT_MICRO27_AUTHORIZATION_TRANCHE"
    )
    assert summary.get("automatic_activation_from_global_progress") is False
    assert summary.get("em_row_id") == "ROW-PILLAR-EM-001"

    mirrored_tokens = [
        "TGC94_EM_MICRO27_DECISION_v0: KEEP_MICRO27_CLOSED_v0",
        "TGC94_EM_MICRO27_AUTHORIZATION_STATUS_v0: NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0",
        "TGC94_EM_MICRO27_REQUIRED_AUTHORIZATION_BASIS_v0: EM_LOCAL_BLOCKER_EVENT_OR_EXPLICIT_MICRO27_AUTHORIZATION_TRANCHE",
        "TGC94_EM_LIVE_ROW_THEOREM_GAP_SIGNAL_v0: ROW_PILLAR_EM_001_REMAINS_LIVE_THEOREM_GAP",
    ]
    missing = [token for token in mirrored_tokens if token not in text]
    assert not missing, "TGC-94 decision package failed to mirror live report token(s): " + ", ".join(missing)


def test_tgc94_decision_package_is_logged_in_ws10_plan() -> None:
    plan_text = _read(PLAN_PATH)
    assert "WS-10-TGC-94 EM Micro-27 authorization parity checkpoint" in plan_text
    assert "formal/docs/release/WS_10_TGC_94_EM_MICRO27_AUTHORIZATION_DECISION_PACKAGE_20260418_v0.md" in plan_text
    assert "KEEP_MICRO27_CLOSED_v0" in plan_text
    assert "NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0" in plan_text