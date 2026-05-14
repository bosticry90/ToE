from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t43_maintenance_selection_report as tool
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_43_DECLARATION_20260418_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t43_maintenance_selection_checkpoint_20260418_v0.json"
REGISTRY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_sliceb_increment_family_registry_20260418_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t43_maintenance_selection_gate.py"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "ws10_t43_maintenance_selection_report.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t43_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, CHECKPOINT_PATH, REGISTRY_PATH, GATE_PATH, TOOL_PATH):
        assert path.exists(), f"Missing required T43 file: {path}"


def test_ws10_t43_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_STATUS_v0: ACTIVE_MAINTENANCE_SELECTION_AND_INDEXING_NONLIVE_v0",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_43_DECLARATION_20260418_v0.md",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_REPORT_TOOL_v0: formal/python/tools/ws10_t43_maintenance_selection_report.py",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_CHECKPOINT_JSON_v0: formal/output/ws10_t43_maintenance_selection_checkpoint_20260418_v0.json",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_RELEASE_REGISTRY_v0: formal/output/reports/qft_gr_sliceb_increment_family_registry_20260418_v0.json",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_GATE_v0: formal/python/tests/test_ws10_t43_maintenance_selection_gate.py",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_ENTRY_CRITERIA_v0: SELECT_ONE_GATE_FAMILY_AND_INDEX_ONE_RELEASE_FAMILY_AGAINST_T42_BASELINE",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_GATE_FAMILY_v0: QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_GATE_STACK",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_RELEASE_FAMILY_v0: QFT_GR_SLICEB_INCREMENT_RELEASE_NOTES",
        "THEORY_RESTART_T43_REMEDIATION_PHASE_Q_NEXT_ACTION_v0: START_QM_STAT_DIRECT_CYCLE_GATE_CONSOLIDATION_AND_OPERATOR_PACK_GENERATION",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t43_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "formal/output/ws10_t43_maintenance_selection_checkpoint_20260418_v0.json",
        "formal/output/reports/qft_gr_sliceb_increment_family_registry_20260418_v0.json",
        "formal/python/tests/test_ws10_t43_maintenance_selection_gate.py",
        "WS10_REMEDIATION_PHASE_Q_T43_STATUS_v0: ACTIVE_MAINTENANCE_SELECTION_AND_INDEXING_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_Q_T43_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_43_DECLARATION_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_Q_T43_REPORT_TOOL_v0: formal/python/tools/ws10_t43_maintenance_selection_report.py",
        "WS10_REMEDIATION_PHASE_Q_T43_CHECKPOINT_JSON_v0: formal/output/ws10_t43_maintenance_selection_checkpoint_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_Q_T43_RELEASE_REGISTRY_v0: formal/output/reports/qft_gr_sliceb_increment_family_registry_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_Q_T43_GATE_v0: formal/python/tests/test_ws10_t43_maintenance_selection_gate.py",
        "WS10_REMEDIATION_PHASE_Q_T43_ENTRY_CRITERIA_v0: SELECT_ONE_GATE_FAMILY_AND_INDEX_ONE_RELEASE_FAMILY_AGAINST_T42_BASELINE",
        "WS10_REMEDIATION_PHASE_Q_T43_GATE_FAMILY_v0: QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_GATE_STACK",
        "WS10_REMEDIATION_PHASE_Q_T43_RELEASE_FAMILY_v0: QFT_GR_SLICEB_INCREMENT_RELEASE_NOTES",
        "WS10_REMEDIATION_PHASE_Q_T43_NEXT_ACTION_v0: START_QM_STAT_DIRECT_CYCLE_GATE_CONSOLIDATION_AND_OPERATOR_PACK_GENERATION",
        "WS10_REMEDIATION_PHASE_Q_T43_ADJUDICATION_v0: MAINTENANCE_TARGETS_SELECTED_AND_RELEASE_FAMILY_INDEXED_NONLIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase Q T43 token(s): " + ", ".join(missing)


def test_ws10_t43_generated_artifacts_match_tool_output() -> None:
    registry = _json(REGISTRY_PATH)
    checkpoint = _json(CHECKPOINT_PATH)
    expected_registry = tool.build_release_family_registry(captured_at_utc=registry.get("captured_at_utc"))
    expected_checkpoint = tool.build_checkpoint(registry=expected_registry, captured_at_utc=checkpoint.get("captured_at_utc"))
    assert registry == expected_registry, "T43 release-family registry drifted from generator output."
    assert checkpoint == expected_checkpoint, "T43 maintenance-selection checkpoint drifted from generator output."


def test_ws10_t43_selection_semantics() -> None:
    checkpoint = _json(CHECKPOINT_PATH)
    registry = _json(REGISTRY_PATH)

    assert checkpoint.get("status") == "ACTIVE_MAINTENANCE_SELECTION_AND_INDEXING_NONLIVE_v0"
    assert checkpoint.get("selected_gate_family", {}).get("direct_cycle_gate_count", 0) >= 10
    assert checkpoint.get("selected_gate_family", {}).get("synthesis_gate_count", 0) >= 10
    assert checkpoint.get("baseline_reference", {}).get("t42_governed_pytests_expected_count") == 346
    assert checkpoint.get("selected_release_family", {}).get("file_count") == registry.get("file_count")
    assert checkpoint.get("summary", {}).get("terminal_outcome") == "MAINTENANCE_FAMILIES_SELECTED_AND_QFT_GR_RELEASE_FAMILY_INDEXED"

    assert registry.get("family_id") == "QFT_GR_SLICEB_INCREMENT_RELEASE_NOTES"
    assert registry.get("file_count", 0) > 200
    counts = registry.get("counts_by_kind", {})
    assert counts.get("ASSESSMENT_NOTE", 0) > 0
    assert counts.get("EXECUTION_PACKET", 0) > 0
    assert counts.get("SEMANTIC_DELTA_DECISION_NOTE", 0) > 0
    assert counts.get("SYNTHESIS_NOTE", 0) > 0
