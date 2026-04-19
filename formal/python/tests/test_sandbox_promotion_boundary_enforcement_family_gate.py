from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import sandbox_promotion_boundary_enforcement_family_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_MIGRATION_PHASE5_IMPLEMENTATION_20260419_v0.md"
FAMILY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "sandbox_promotion_boundary_enforcement_family_20260419_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase5_closeout_files_exist() -> None:
    for path in (DECLARATION_PATH, FAMILY_PATH, REPORT_PATH):
        assert path.exists(), f"Missing required Phase 5 closeout file: {path}"


def test_phase5_declaration_structure() -> None:
    text = _read(DECLARATION_PATH)
    for section in (
        "## Tranche name",
        "## Objective",
        "## Allowed files",
        "## Out of scope",
        "## Acceptance",
        "## Rollback anchor",
        "## Hard stop rule",
        "## Boundary freshness note",
    ):
        assert section in text


def test_boundary_family_surface_tokens_and_gates_present() -> None:
    text = _read(FAMILY_PATH)
    for token in (
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_SCOPE_v0: POLICY_SPLIT_PLUS_SCHEMA_PAYLOAD_PLUS_GOVERNED_AUDIT_PLUS_AUTHORITY_CUTOVER_PLUS_POST_PILOT_NONWIDENED_BOUNDARY",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_GATES_v0: LANE_POLICY_PLUS_PHASE2_PHASE4_PLUS_PHASE2_PHASE6_PLUS_AUTHORITY_CUTOVER_PLUS_PHASE7_PHASE3_PLUS_PHASE5_CLOSEOUT",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAIL_CLOSED_RULE_v0: ANY_MISSING_BOUNDARY_SURFACE_GATE_POINTER_OR_NONWIDENED_HOLD_DRIFT_BLOCKS_PHASE5_CLOSEOUT",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_TOOL_v0: formal/python/tools/sandbox_promotion_boundary_enforcement_family_report.py",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_JSON_v0: formal/output/reports/sandbox_promotion_boundary_enforcement_family_20260419_v0.json",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
    ):
        assert token in text

    for path_ref in (
        "formal/python/tests/test_sandbox_promotion_lane_policy_gate.py",
        "formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py",
        "formal/python/tests/test_sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py",
        "formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
        "formal/python/tests/test_sandbox_promotion_post_pilot_decision_phase3_followthrough_gate.py",
        "formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
    ):
        assert path_ref in text


def test_phase5_report_matches_tool_output() -> None:
    payload = _read_json(REPORT_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "Phase 5 boundary-enforcement family report drifted from generator output."


def test_phase5_mirror_tokens_present_and_complete() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    for token in (
        "SANDBOX_PROMOTION_PHASE5_IMPLEMENTATION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE5_IMPLEMENTATION_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_TOOL_v0: formal/python/tools/sandbox_promotion_boundary_enforcement_family_report.py",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_v0: formal/output/reports/sandbox_promotion_boundary_enforcement_family_20260419_v0.json",
        "SANDBOX_PROMOTION_PHASE5_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
        "SANDBOX_PROMOTION_MIGRATION_PHASE5_STATUS_v0: OBJECTIVELY_COMPLETE_BOUNDARY_ENFORCEMENT_FAMILY_AND_FAIL_CLOSED_CLOSEOUT_GATE_PINNED",
        "SANDBOX_PROMOTION_ARCHITECTURE_NEXT_ACTION_v0: ROUTE_FUTURE_BOUNDED_WORK_THROUGH_COMPLETED_SANDBOX_PROMOTION_GOVERNANCE_STACK",
    ):
        assert token in state_text
        assert token in roadmap_text

    payload = _read_json(REPORT_PATH)
    assert payload["summary"]["closeout_status"] == "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_COMPLETE"