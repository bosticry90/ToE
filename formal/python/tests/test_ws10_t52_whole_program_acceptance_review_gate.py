from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t52_whole_program_acceptance_review_report as tool


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_52_DECLARATION_20260419_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t52_whole_program_acceptance_review_20260419_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t52_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, REPORT_PATH):
        assert path.exists(), f"Missing required T52 file: {path}"


def test_ws10_t52_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_STATUS_v0: ACTIVE_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_NONLIVE_v0",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_52_DECLARATION_20260419_v0.md",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_T51_REPORT_v0: formal/output/reports/ws10_t51_post_plan_authority_source_cutover_20260419_v0.json",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_REPORT_TOOL_v0: formal/python/tools/ws10_t52_whole_program_acceptance_review_report.py",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_REPORT_JSON_v0: formal/output/reports/ws10_t52_whole_program_acceptance_review_20260419_v0.json",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_GATE_v0: formal/python/tests/test_ws10_t52_whole_program_acceptance_review_gate.py",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_ENTRY_CRITERIA_v0: REQUIRE_T51_CUTOVER_PLUS_CHECKPOINT_LADDER_AND_GOVERNANCE_ACCEPTANCE_SURFACES_PLUS_POST_PLAN_PHASE6_HOLD_REVIEW",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_LADDER_SURFACE_v0: formal/output/reports/checkpoint_ladder_acceptance_summary_v0.json",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_CUTOVER_SURFACE_v0: formal/output/reports/dual_track_cutover_report_v0.json",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_WHOLE_PROGRAM_OUTCOME_v0: WS10_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT_v0",
        "THEORY_RESTART_T52_POST_PLAN_PHASE_Z_NEXT_ACTION_v0: KEEP_PHASE6_HELD_AND_REQUIRE_NEW_BLOCKER_MOVEMENT_BEFORE_WHOLE_PROGRAM_ACCEPT_OR_REJECT_CLOSEOUT",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t52_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_Z_T52_STATUS_v0: ACTIVE_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_Z_T52_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_52_DECLARATION_20260419_v0.md",
        "WS10_REMEDIATION_PHASE_Z_T52_T51_REPORT_v0: formal/output/reports/ws10_t51_post_plan_authority_source_cutover_20260419_v0.json",
        "WS10_REMEDIATION_PHASE_Z_T52_REPORT_TOOL_v0: formal/python/tools/ws10_t52_whole_program_acceptance_review_report.py",
        "WS10_REMEDIATION_PHASE_Z_T52_REPORT_JSON_v0: formal/output/reports/ws10_t52_whole_program_acceptance_review_20260419_v0.json",
        "WS10_REMEDIATION_PHASE_Z_T52_GATE_v0: formal/python/tests/test_ws10_t52_whole_program_acceptance_review_gate.py",
        "WS10_REMEDIATION_PHASE_Z_T52_ENTRY_CRITERIA_v0: REQUIRE_T51_CUTOVER_PLUS_CHECKPOINT_LADDER_AND_GOVERNANCE_ACCEPTANCE_SURFACES_PLUS_POST_PLAN_PHASE6_HOLD_REVIEW",
        "WS10_REMEDIATION_PHASE_Z_T52_LADDER_SURFACE_v0: formal/output/reports/checkpoint_ladder_acceptance_summary_v0.json",
        "WS10_REMEDIATION_PHASE_Z_T52_CUTOVER_SURFACE_v0: formal/output/reports/dual_track_cutover_report_v0.json",
        "WS10_REMEDIATION_PHASE_Z_T52_WHOLE_PROGRAM_OUTCOME_v0: WS10_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT_v0",
        "WS10_REMEDIATION_PHASE_Z_T52_NEXT_ACTION_v0: KEEP_PHASE6_HELD_AND_REQUIRE_NEW_BLOCKER_MOVEMENT_BEFORE_WHOLE_PROGRAM_ACCEPT_OR_REJECT_CLOSEOUT",
        "WS10_REMEDIATION_PHASE_Z_T52_ADJUDICATION_v0: WHOLE_PROGRAM_ACCEPTANCE_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase Z T52 token(s): " + ", ".join(missing)


def test_ws10_t52_report_matches_tool_output() -> None:
    payload = _json(REPORT_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "T52 whole-program acceptance review report drifted from generator output."


def test_ws10_t52_report_semantics() -> None:
    payload = _json(REPORT_PATH)
    assert payload.get("status") == "ACTIVE_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_NONLIVE_v0"
    assert all(payload.get("criteria", {}).values())
    assert payload.get("summary", {}).get("terminal_outcome") == "WS10_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT_v0"
    assert payload.get("summary", {}).get("acceptance_stack_status") == "GREEN_BUT_NONPROMOTION"
    assert payload.get("summary", {}).get("post_plan_phase6_outcome") == "POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT"
