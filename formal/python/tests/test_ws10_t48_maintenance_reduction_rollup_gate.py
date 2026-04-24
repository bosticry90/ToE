from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t48_maintenance_reduction_rollup_report as tool
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_48_DECLARATION_20260418_v0.md"
ROLLUP_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_maintenance_reduction_rollup_20260418_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t48_maintenance_reduction_rollup_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t48_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, ROLLUP_PATH, GATE_PATH):
        assert path.exists(), f"Missing required T48 file: {path}"


def test_ws10_t48_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T48_REMEDIATION_PHASE_V_STATUS_v0: ACTIVE_MAINTENANCE_ROLLUP_AND_REVIEW_DEFAULTS_NONLIVE_v0",
        "THEORY_RESTART_T48_REMEDIATION_PHASE_V_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_48_DECLARATION_20260418_v0.md",
        "THEORY_RESTART_T48_REMEDIATION_PHASE_V_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T48_REMEDIATION_PHASE_V_REPORT_TOOL_v0: formal/python/tools/ws10_t48_maintenance_reduction_rollup_report.py",
        "THEORY_RESTART_T48_REMEDIATION_PHASE_V_ROLLUP_JSON_v0: formal/output/reports/ws10_maintenance_reduction_rollup_20260418_v0.json",
        "THEORY_RESTART_T48_REMEDIATION_PHASE_V_GATE_v0: formal/python/tests/test_ws10_t48_maintenance_reduction_rollup_gate.py",
        "THEORY_RESTART_T48_REMEDIATION_PHASE_V_ENTRY_CRITERIA_v0: PIN_CUMULATIVE_T44_T46_REDUCTION_AND_DEFAULT_T45_T47_REVIEW_SURFACES_WITH_ENDPOINT06_ADJUDICATION",
        "THEORY_RESTART_T48_REMEDIATION_PHASE_V_NEXT_ACTION_v0: SHIFT_BACK_TO_BLOCKER_MOVING_WORK_UNLESS_ANOTHER_LOW_RISK_REPETITIVE_FAMILY_CLEARLY_MEETS_THE_T44_T46_PATTERN",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t48_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "formal/output/reports/ws10_maintenance_reduction_rollup_20260418_v0.json",
        "formal/python/tools/ws10_t48_maintenance_reduction_rollup_report.py",
        "formal/python/tests/test_ws10_t48_maintenance_reduction_rollup_gate.py",
        "WS10_REMEDIATION_PHASE_V_T48_STATUS_v0: ACTIVE_MAINTENANCE_ROLLUP_AND_REVIEW_DEFAULTS_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_V_T48_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_48_DECLARATION_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_V_T48_REPORT_TOOL_v0: formal/python/tools/ws10_t48_maintenance_reduction_rollup_report.py",
        "WS10_REMEDIATION_PHASE_V_T48_ROLLUP_JSON_v0: formal/output/reports/ws10_maintenance_reduction_rollup_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_V_T48_GATE_v0: formal/python/tests/test_ws10_t48_maintenance_reduction_rollup_gate.py",
        "WS10_REMEDIATION_PHASE_V_T48_ENTRY_CRITERIA_v0: PIN_CUMULATIVE_T44_T46_REDUCTION_AND_DEFAULT_T45_T47_REVIEW_SURFACES_WITH_ENDPOINT06_ADJUDICATION",
        "WS10_REMEDIATION_PHASE_V_T48_NEXT_ACTION_v0: SHIFT_BACK_TO_BLOCKER_MOVING_WORK_UNLESS_ANOTHER_LOW_RISK_REPETITIVE_FAMILY_CLEARLY_MEETS_THE_T44_T46_PATTERN",
        "WS10_REMEDIATION_PHASE_V_T48_ADJUDICATION_v0: MAINTENANCE_ROLLUP_AND_REVIEW_DEFAULTS_PINNED_NONAUTHORITATIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase V T48 token(s): " + ", ".join(missing)


def test_ws10_t48_rollup_matches_tool_output() -> None:
    payload = _json(ROLLUP_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "T48 maintenance rollup drifted from generator output."


def test_ws10_t48_rollup_semantics() -> None:
    payload = _json(ROLLUP_PATH)
    combined = payload.get("maintenance_reduction_rollup", {}).get("combined", {})
    assert payload.get("status") == "DERIVED_ROLLUP_AND_EXECUTION_WINDOW_DEFAULTS_v0"
    assert combined.get("pre_refactor_lines") == 3198
    assert combined.get("helper_backed_wrapper_count") == 19
    assert combined.get("post_refactor_lines", 0) < combined.get("pre_refactor_lines", 0)
    assert combined.get("net_line_reduction", 0) > 2200
    assert combined.get("reduction_ratio", 0) > 0.70
    defaults = payload.get("execution_window_defaults", {})
    assert defaults.get("operator_review_surface", {}).get("artifact_pointer") == "formal/output/reports/ws10_operator_truth_pack_20260418_v0.json"
    assert defaults.get("release_family_review_surface", {}).get("artifact_pointer") == "formal/output/reports/qft_gr_sliceb_increment_family_summary_views_20260418_v0.json"
    endpoint = payload.get("synthesis_endpoint_06_adjudication", {})
    assert endpoint.get("missing_end_increment") == 6
    assert endpoint.get("pointer_exists") is False
    assert endpoint.get("adjudication") == "INTENTIONAL_SYNTHESIS_CHECKPOINT_OMISSION_v0"
    assert payload.get("summary", {}).get("terminal_outcome") == "CUMULATIVE_MAINTENANCE_REDUCTION_AND_REVIEW_DEFAULTS_PINNED"
