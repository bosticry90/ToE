from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t45_operator_truth_pack_report as tool


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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_45_DECLARATION_20260418_v0.md"
PACK_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_operator_truth_pack_20260418_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t45_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, PACK_PATH):
        assert path.exists(), f"Missing required T45 file: {path}"


def test_ws10_t45_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T45_REMEDIATION_PHASE_S_STATUS_v0: ACTIVE_OPERATOR_TRUTH_PACK_NONLIVE_v0",
        "THEORY_RESTART_T45_REMEDIATION_PHASE_S_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_45_DECLARATION_20260418_v0.md",
        "THEORY_RESTART_T45_REMEDIATION_PHASE_S_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T45_REMEDIATION_PHASE_S_REPORT_TOOL_v0: formal/python/tools/ws10_t45_operator_truth_pack_report.py",
        "THEORY_RESTART_T45_REMEDIATION_PHASE_S_PACK_JSON_v0: formal/output/reports/ws10_operator_truth_pack_20260418_v0.json",
        "THEORY_RESTART_T45_REMEDIATION_PHASE_S_GATE_v0: formal/python/tests/test_ws10_t45_operator_truth_pack_gate.py",
        "THEORY_RESTART_T45_REMEDIATION_PHASE_S_ENTRY_CRITERIA_v0: SUMMARIZE_T42_T43_T44_AND_CONTROL_SURFACES_WITHOUT_REPLACING_AUTHORITY",
        "THEORY_RESTART_T45_REMEDIATION_PHASE_S_NEXT_ACTION_v0: CONSOLIDATE_QM_STAT_SYNTHESIS_GATES_AND_EXTEND_RELEASE_FAMILY_SUMMARY_VIEWS",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t45_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "formal/output/reports/ws10_operator_truth_pack_20260418_v0.json",
        "formal/python/tools/ws10_t45_operator_truth_pack_report.py",
        "formal/python/tests/test_ws10_t45_operator_truth_pack_gate.py",
        "WS10_REMEDIATION_PHASE_S_T45_STATUS_v0: ACTIVE_OPERATOR_TRUTH_PACK_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_S_T45_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_45_DECLARATION_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_S_T45_REPORT_TOOL_v0: formal/python/tools/ws10_t45_operator_truth_pack_report.py",
        "WS10_REMEDIATION_PHASE_S_T45_PACK_JSON_v0: formal/output/reports/ws10_operator_truth_pack_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_S_T45_GATE_v0: formal/python/tests/test_ws10_t45_operator_truth_pack_gate.py",
        "WS10_REMEDIATION_PHASE_S_T45_ENTRY_CRITERIA_v0: SUMMARIZE_T42_T43_T44_AND_CONTROL_SURFACES_WITHOUT_REPLACING_AUTHORITY",
        "WS10_REMEDIATION_PHASE_S_T45_NEXT_ACTION_v0: CONSOLIDATE_QM_STAT_SYNTHESIS_GATES_AND_EXTEND_RELEASE_FAMILY_SUMMARY_VIEWS",
        "WS10_REMEDIATION_PHASE_S_T45_ADJUDICATION_v0: OPERATOR_TRUTH_PACK_GENERATED_NONAUTHORITATIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase S T45 token(s): " + ", ".join(missing)


def test_ws10_t45_pack_matches_tool_output() -> None:
    payload = _json(PACK_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "T45 operator truth-pack drifted from generator output."


def test_ws10_t45_pack_semantics() -> None:
    payload = _json(PACK_PATH)
    assert payload.get("status") == "NONAUTHORITATIVE_OPERATOR_REVIEW_PACKET_v0"
    assert payload.get("tranche_stack", {}).get("t43_selected_gate_family", {}).get("family_id") == "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_GATE_STACK"
    assert payload.get("review_focus", {}).get("next_gate_reduction_lane") == "QM_STAT_SYNTHESIS_GATES"
    assert payload.get("review_focus", {}).get("indexed_release_family", {}).get("file_count") == 279
    assert payload.get("summary", {}).get("terminal_outcome") == "OPERATOR_TRUTH_PACK_GENERATED_OVER_T42_T43_T44_AND_CONTROL_SURFACES"