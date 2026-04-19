from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t50_post_plan_phase3_to_phase6_alignment_report as tool


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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_50_DECLARATION_20260418_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t50_post_plan_phase3_to_phase6_alignment_20260418_v0.json"
POST_PLAN_PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t50_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, REPORT_PATH, POST_PLAN_PROGRAM_PATH):
        assert path.exists(), f"Missing required T50 file: {path}"


def test_ws10_t50_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_STATUS_v0: ACTIVE_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_NONLIVE_v0",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_50_DECLARATION_20260418_v0.md",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_SOURCE_PROGRAM_v0: formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_REPORT_TOOL_v0: formal/python/tools/ws10_t50_post_plan_phase3_to_phase6_alignment_report.py",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_REPORT_JSON_v0: formal/output/reports/ws10_t50_post_plan_phase3_to_phase6_alignment_20260418_v0.json",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_GATE_v0: formal/python/tests/test_ws10_t50_post_plan_phase3_to_phase6_alignment_gate.py",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_ENTRY_CRITERIA_v0: ALIGN_EXISTING_POST_PLAN_PHASE3_TO_PHASE6_OUTCOMES_WITH_ACTIVE_WS10_CHAIN",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_PHASE3_QM_OUTCOME_v0: POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_NONPROMOTED",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_PHASE4_SEAM_OUTCOME_v0: POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_PHASE5_MASTER_ACTION_OUTCOME_v0: POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_PHASE6_INTEGRATION_OUTCOME_v0: POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT",
        "THEORY_RESTART_T50_POST_PLAN_PHASE_X_NEXT_ACTION_v0: EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_BEFORE_ANY_DOWNSTREAM_RECLASSIFICATION",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t50_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "formal/output/reports/ws10_t50_post_plan_phase3_to_phase6_alignment_20260418_v0.json",
        "formal/python/tools/ws10_t50_post_plan_phase3_to_phase6_alignment_report.py",
        "formal/python/tests/test_ws10_t50_post_plan_phase3_to_phase6_alignment_gate.py",
        "WS10_REMEDIATION_PHASE_X_T50_STATUS_v0: ACTIVE_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_X_T50_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_50_DECLARATION_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_X_T50_REPORT_TOOL_v0: formal/python/tools/ws10_t50_post_plan_phase3_to_phase6_alignment_report.py",
        "WS10_REMEDIATION_PHASE_X_T50_REPORT_JSON_v0: formal/output/reports/ws10_t50_post_plan_phase3_to_phase6_alignment_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_X_T50_GATE_v0: formal/python/tests/test_ws10_t50_post_plan_phase3_to_phase6_alignment_gate.py",
        "WS10_REMEDIATION_PHASE_X_T50_SOURCE_PROGRAM_v0: formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_X_T50_ENTRY_CRITERIA_v0: ALIGN_EXISTING_POST_PLAN_PHASE3_TO_PHASE6_OUTCOMES_WITH_ACTIVE_WS10_CHAIN",
        "WS10_REMEDIATION_PHASE_X_T50_PHASE3_QM_OUTCOME_v0: POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_NONPROMOTED",
        "WS10_REMEDIATION_PHASE_X_T50_PHASE4_SEAM_OUTCOME_v0: POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
        "WS10_REMEDIATION_PHASE_X_T50_PHASE5_MASTER_ACTION_OUTCOME_v0: POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
        "WS10_REMEDIATION_PHASE_X_T50_PHASE6_INTEGRATION_OUTCOME_v0: POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT",
        "WS10_REMEDIATION_PHASE_X_T50_NEXT_ACTION_v0: EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_BEFORE_ANY_DOWNSTREAM_RECLASSIFICATION",
        "WS10_REMEDIATION_PHASE_X_T50_ADJUDICATION_v0: POST_PLAN_PHASE3_TO_PHASE6_STATUS_CHAIN_PINNED_NONLIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase X T50 token(s): " + ", ".join(missing)


def test_ws10_t50_declaration_structure() -> None:
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


def test_ws10_t50_report_matches_tool_output() -> None:
    payload = _json(REPORT_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "T50 post-plan phase3-to-phase6 alignment report drifted from generator output."


def test_ws10_t50_report_semantics() -> None:
    payload = _json(REPORT_PATH)
    criteria = payload.get("criteria", {})
    summary = payload.get("summary", {})
    assert payload.get("status") == "ACTIVE_POST_PLAN_PHASE3_TO_PHASE6_ALIGNMENT_NONLIVE_v0"
    assert all(criteria.values())
    assert summary.get("terminal_outcome") == "WS10_POST_PLAN_PHASE3_TO_PHASE6_STATUS_CHAIN_PINNED_NONLIVE_v0"
    assert summary.get("phase3_terminal_outcome") == "POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_NONPROMOTED"
    assert summary.get("phase6_terminal_outcome") == "POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT"
    assert summary.get("next_action") == "EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_BEFORE_ANY_DOWNSTREAM_RECLASSIFICATION"