from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t44_qm_stat_direct_cycle_consolidation_report as tool


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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_44_DECLARATION_20260418_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0.json"
HELPER_PATH = REPO_ROOT / "formal" / "python" / "tests" / "qm_stat_class_b_cycle_gate_family_helper.py"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t44_qm_stat_direct_cycle_consolidation_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t44_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, CHECKPOINT_PATH, HELPER_PATH, GATE_PATH):
        assert path.exists(), f"Missing required T44 file: {path}"


def test_ws10_t44_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_STATUS_v0: ACTIVE_QM_STAT_DIRECT_CYCLE_CONSOLIDATION_NONLIVE_v0",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_44_DECLARATION_20260418_v0.md",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_REPORT_TOOL_v0: formal/python/tools/ws10_t44_qm_stat_direct_cycle_consolidation_report.py",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_CHECKPOINT_JSON_v0: formal/output/ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0.json",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_HELPER_v0: formal/python/tests/qm_stat_class_b_cycle_gate_family_helper.py",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_GATE_v0: formal/python/tests/test_ws10_t44_qm_stat_direct_cycle_consolidation_gate.py",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_ENTRY_CRITERIA_v0: COLLAPSE_QM_STAT_DIRECT_CYCLE_GATES_WITHOUT_TOUCHING_SYNTHESIS_OR_BESPOKE_BOUNDARIES",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_REDUCTION_BASELINE_v0: T43_SELECTED_QM_STAT_DIRECT_CYCLE_FAMILY",
        "THEORY_RESTART_T44_REMEDIATION_PHASE_R_NEXT_ACTION_v0: GENERATE_OPERATOR_TRUTH_PACK_FROM_T42_T43_T44_AND_BLOCKER_SURFACES",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t44_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "formal/output/ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0.json",
        "formal/python/tools/ws10_t44_qm_stat_direct_cycle_consolidation_report.py",
        "formal/python/tests/qm_stat_class_b_cycle_gate_family_helper.py",
        "formal/python/tests/test_ws10_t44_qm_stat_direct_cycle_consolidation_gate.py",
        "WS10_REMEDIATION_PHASE_R_T44_STATUS_v0: ACTIVE_QM_STAT_DIRECT_CYCLE_CONSOLIDATION_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_R_T44_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_44_DECLARATION_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_R_T44_REPORT_TOOL_v0: formal/python/tools/ws10_t44_qm_stat_direct_cycle_consolidation_report.py",
        "WS10_REMEDIATION_PHASE_R_T44_CHECKPOINT_JSON_v0: formal/output/ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_R_T44_HELPER_v0: formal/python/tests/qm_stat_class_b_cycle_gate_family_helper.py",
        "WS10_REMEDIATION_PHASE_R_T44_GATE_v0: formal/python/tests/test_ws10_t44_qm_stat_direct_cycle_consolidation_gate.py",
        "WS10_REMEDIATION_PHASE_R_T44_ENTRY_CRITERIA_v0: COLLAPSE_QM_STAT_DIRECT_CYCLE_GATES_WITHOUT_TOUCHING_SYNTHESIS_OR_BESPOKE_BOUNDARIES",
        "WS10_REMEDIATION_PHASE_R_T44_REDUCTION_BASELINE_v0: T43_SELECTED_QM_STAT_DIRECT_CYCLE_FAMILY",
        "WS10_REMEDIATION_PHASE_R_T44_NEXT_ACTION_v0: GENERATE_OPERATOR_TRUTH_PACK_FROM_T42_T43_T44_AND_BLOCKER_SURFACES",
        "WS10_REMEDIATION_PHASE_R_T44_ADJUDICATION_v0: QM_STAT_DIRECT_CYCLE_EXECUTABLE_DUPLICATION_REDUCED_NONLIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase R T44 token(s): " + ", ".join(missing)


def test_ws10_t44_generated_checkpoint_matches_tool_output() -> None:
    payload = _json(CHECKPOINT_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "T44 consolidation checkpoint drifted from generator output."


def test_ws10_t44_checkpoint_semantics() -> None:
    payload = _json(CHECKPOINT_PATH)
    metrics = payload.get("consolidation_metrics", {})
    assert payload.get("status") == "ACTIVE_QM_STAT_DIRECT_CYCLE_CONSOLIDATION_NONLIVE_v0"
    assert payload.get("baseline_reference", {}).get("pre_refactor_helperizable_direct_cycle_lines") == 1741
    assert metrics.get("helper_backed_wrapper_count") == 10
    assert metrics.get("helper_lines") > 0
    assert metrics.get("post_refactor_total_lines") == 430
    assert metrics.get("net_line_reduction") == 1311
    assert payload.get("summary", {}).get("terminal_outcome") == "QM_STAT_DIRECT_CYCLE_GATES_CONSOLIDATED_ON_SHARED_HELPER"