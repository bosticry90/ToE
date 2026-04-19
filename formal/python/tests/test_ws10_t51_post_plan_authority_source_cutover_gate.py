from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t51_post_plan_authority_source_cutover_report as tool


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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_51_DECLARATION_20260419_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t51_post_plan_authority_source_cutover_20260419_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t51_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, REPORT_PATH):
        assert path.exists(), f"Missing required T51 file: {path}"


def test_ws10_t51_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_STATUS_v0: ACTIVE_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_NONLIVE_v0",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_51_DECLARATION_20260419_v0.md",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_CONSOLIDATION_MEMO_v0: formal/docs/release/POST_PLAN_CONSOLIDATION_MEMO_20260418_v0.md",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_REPORT_TOOL_v0: formal/python/tools/ws10_t51_post_plan_authority_source_cutover_report.py",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_REPORT_JSON_v0: formal/output/reports/ws10_t51_post_plan_authority_source_cutover_20260419_v0.json",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_GATE_v0: formal/python/tests/test_ws10_t51_post_plan_authority_source_cutover_gate.py",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_ENTRY_CRITERIA_v0: REQUIRE_T50_ALIGNMENT_PLUS_CONSOLIDATION_MEMO_SINGLE_SOURCE_GOVERNANCE_READ",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_CUTOVER_RESULT_v0: PHASE3_TO_PHASE6_CONTROL_STACK_GOVERNS_CURRENT_REPO_READS",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_LEGACY_RESTART_STATUS_v0: WS10_RESTART_SURFACES_RETAINED_FOR_TRACEABILITY_ONLY",
        "THEORY_RESTART_T51_POST_PLAN_PHASE_Y_NEXT_ACTION_v0: RUN_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_AGAINST_POST_PLAN_AUTHORITY_CUTOVER",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t51_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_Y_T51_STATUS_v0: ACTIVE_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_Y_T51_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_51_DECLARATION_20260419_v0.md",
        "WS10_REMEDIATION_PHASE_Y_T51_CONSOLIDATION_MEMO_v0: formal/docs/release/POST_PLAN_CONSOLIDATION_MEMO_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_Y_T51_REPORT_TOOL_v0: formal/python/tools/ws10_t51_post_plan_authority_source_cutover_report.py",
        "WS10_REMEDIATION_PHASE_Y_T51_REPORT_JSON_v0: formal/output/reports/ws10_t51_post_plan_authority_source_cutover_20260419_v0.json",
        "WS10_REMEDIATION_PHASE_Y_T51_GATE_v0: formal/python/tests/test_ws10_t51_post_plan_authority_source_cutover_gate.py",
        "WS10_REMEDIATION_PHASE_Y_T51_ENTRY_CRITERIA_v0: REQUIRE_T50_ALIGNMENT_PLUS_CONSOLIDATION_MEMO_SINGLE_SOURCE_GOVERNANCE_READ",
        "WS10_REMEDIATION_PHASE_Y_T51_CUTOVER_RESULT_v0: PHASE3_TO_PHASE6_CONTROL_STACK_GOVERNS_CURRENT_REPO_READS",
        "WS10_REMEDIATION_PHASE_Y_T51_LEGACY_RESTART_STATUS_v0: WS10_RESTART_SURFACES_RETAINED_FOR_TRACEABILITY_ONLY",
        "WS10_REMEDIATION_PHASE_Y_T51_NEXT_ACTION_v0: RUN_WHOLE_PROGRAM_ACCEPTANCE_REVIEW_AGAINST_POST_PLAN_AUTHORITY_CUTOVER",
        "WS10_REMEDIATION_PHASE_Y_T51_ADJUDICATION_v0: POST_PLAN_AUTHORITY_SOURCE_CUTOVER_PINNED_NONLIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase Y T51 token(s): " + ", ".join(missing)


def test_ws10_t51_report_matches_tool_output() -> None:
    payload = _json(REPORT_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "T51 authority-source cutover report drifted from generator output."


def test_ws10_t51_report_semantics() -> None:
    payload = _json(REPORT_PATH)
    assert payload.get("status") == "ACTIVE_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_NONLIVE_v0"
    assert all(payload.get("criteria", {}).values())
    assert payload.get("summary", {}).get("terminal_outcome") == "WS10_POST_PLAN_AUTHORITY_SOURCE_CUTOVER_PINNED_NONLIVE_v0"
    assert payload.get("summary", {}).get("cutover_result") == "PHASE3_TO_PHASE6_CONTROL_STACK_GOVERNS_CURRENT_REPO_READS"
    assert payload.get("summary", {}).get("legacy_restart_status") == "WS10_RESTART_SURFACES_RETAINED_FOR_TRACEABILITY_ONLY"
