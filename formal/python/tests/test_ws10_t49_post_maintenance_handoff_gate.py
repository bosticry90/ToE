from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t49_post_maintenance_handoff_report as tool
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_49_DECLARATION_20260418_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t49_post_maintenance_handoff_20260418_v0.json"
POST_PLAN_PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t49_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, REPORT_PATH, POST_PLAN_PROGRAM_PATH):
        assert path.exists(), f"Missing required T49 file: {path}"


def test_ws10_t49_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_STATUS_v0: ACTIVE_POST_MAINTENANCE_HANDOFF_NONLIVE_v0",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_49_DECLARATION_20260418_v0.md",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_HANDOFF_PROGRAM_v0: formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_REPORT_TOOL_v0: formal/python/tools/ws10_t49_post_maintenance_handoff_report.py",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_REPORT_JSON_v0: formal/output/reports/ws10_t49_post_maintenance_handoff_20260418_v0.json",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_GATE_v0: formal/python/tests/test_ws10_t49_post_maintenance_handoff_gate.py",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_ENTRY_CRITERIA_v0: CONFIRM_T48_REVIEW_DEFAULTS_AND_HAND_OFF_TO_POST_PLAN_TARGET_MAP_AND_COSMO_SR_TRANCHE",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_SOLE_EXECUTABLE_ROW_v0: ROW-SEAM-COSMO-SR-001",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_BLOCKED_AUTHORITY_ROW_v0: ROW-SEAM-QM-STAT-001",
        "THEORY_RESTART_T49_POST_MAINTENANCE_PHASE_W_NEXT_ACTION_v0: RETAIN_COSMO_SR_AS_SOLE_EXECUTABLE_ROW_AND_REQUIRE_NEW_ROW_MOVEMENT_BEFORE_REROUTE",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t49_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "formal/output/reports/ws10_t49_post_maintenance_handoff_20260418_v0.json",
        "formal/python/tools/ws10_t49_post_maintenance_handoff_report.py",
        "formal/python/tests/test_ws10_t49_post_maintenance_handoff_gate.py",
        "WS10_REMEDIATION_PHASE_W_T49_STATUS_v0: ACTIVE_POST_MAINTENANCE_HANDOFF_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_W_T49_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_49_DECLARATION_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_W_T49_REPORT_TOOL_v0: formal/python/tools/ws10_t49_post_maintenance_handoff_report.py",
        "WS10_REMEDIATION_PHASE_W_T49_REPORT_JSON_v0: formal/output/reports/ws10_t49_post_maintenance_handoff_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_W_T49_GATE_v0: formal/python/tests/test_ws10_t49_post_maintenance_handoff_gate.py",
        "WS10_REMEDIATION_PHASE_W_T49_HANDOFF_PROGRAM_v0: formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_W_T49_ENTRY_CRITERIA_v0: CONFIRM_T48_REVIEW_DEFAULTS_AND_HAND_OFF_TO_POST_PLAN_TARGET_MAP_AND_COSMO_SR_TRANCHE",
        "WS10_REMEDIATION_PHASE_W_T49_SOLE_EXECUTABLE_ROW_v0: ROW-SEAM-COSMO-SR-001",
        "WS10_REMEDIATION_PHASE_W_T49_BLOCKED_AUTHORITY_ROW_v0: ROW-SEAM-QM-STAT-001",
        "WS10_REMEDIATION_PHASE_W_T49_NEXT_ACTION_v0: RETAIN_COSMO_SR_AS_SOLE_EXECUTABLE_ROW_AND_REQUIRE_NEW_ROW_MOVEMENT_BEFORE_REROUTE",
        "WS10_REMEDIATION_PHASE_W_T49_ADJUDICATION_v0: POST_MAINTENANCE_HANDOFF_TO_POST_PLAN_EXECUTION_PINNED_NONLIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase W T49 token(s): " + ", ".join(missing)


def test_ws10_t49_declaration_structure() -> None:
    text = _read(DECLARATION_PATH)
    required_sections = [
        "## Tranche name",
        "## Objective",
        "## Allowed files",
        "## Out of scope",
        "## Acceptance",
        "## Rollback anchor",
        "## Hard stop rule",
        "## Boundary freshness note",
    ]
    for section in required_sections:
        assert section in text, f"Missing declaration section: {section}"


def test_ws10_t49_report_matches_tool_output() -> None:
    payload = _json(REPORT_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "T49 post-maintenance handoff report drifted from generator output."


def test_ws10_t49_report_semantics() -> None:
    payload = _json(REPORT_PATH)
    criteria = payload.get("criteria", {})
    summary = payload.get("summary", {})
    assert payload.get("status") == "ACTIVE_POST_MAINTENANCE_HANDOFF_NONLIVE_v0"
    assert all(criteria.values())
    assert summary.get("terminal_outcome") == "WS10_POST_MAINTENANCE_HANDOFF_TO_POST_PLAN_EXECUTION_PINNED_NONLIVE_v0"
    assert summary.get("active_post_plan_program") == "formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"
    assert summary.get("sole_executable_row") == "ROW-SEAM-COSMO-SR-001"
    assert summary.get("blocked_authority_row") == "ROW-SEAM-QM-STAT-001"
    assert summary.get("next_action") == "RETAIN_COSMO_SR_AS_SOLE_EXECUTABLE_ROW_AND_REQUIRE_NEW_ROW_MOVEMENT_BEFORE_REROUTE"