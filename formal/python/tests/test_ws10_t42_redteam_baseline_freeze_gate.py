from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t42_redteam_baseline_freeze_report as tool


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
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_42_DECLARATION_20260418_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t42_redteam_baseline_freeze_gate.py"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "ws10_t42_redteam_baseline_freeze_report.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t42_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 42 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing T42 checkpoint artifact."
    assert TOOL_PATH.exists(), "Missing T42 report tool."
    assert GATE_PATH.exists(), "Missing T42 gate file."


def test_ws10_t42_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_STATUS_v0: ACTIVE_REDTEAM_BASELINE_FREEZE_NONLIVE_v0",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_42_DECLARATION_20260418_v0.md",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_REPORT_TOOL_v0: formal/python/tools/ws10_t42_redteam_baseline_freeze_report.py",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_CHECKPOINT_JSON_v0: formal/output/ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0.json",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_GATE_v0: formal/python/tests/test_ws10_t42_redteam_baseline_freeze_gate.py",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_ENTRY_CRITERIA_v0: REFRESH_BASELINE_COUNTS_AND_PIN_FREEZE_RULES_WITHOUT_LIVE_EXECUTION_CHANGE",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_PRIMARY_METRICS_v0: THEOREM_GAP_PLUS_SEAM_GAP_PLUS_BLOCKER_NET_DELTA",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_RELEASE_SURFACE_RULE_v0: NO_NEW_RELEASE_FAMILY_GROWTH_WITHOUT_RETIREMENT_OR_CANONICAL_BLOCKER_CLOSURE",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_GOVERNED_PYTEST_RULE_v0: NO_NEW_GOVERNED_PYTEST_GROWTH_WITHOUT_MANIFEST_JUSTIFIED_RETIREMENT_OR_CANONICAL_BLOCKER_CLOSURE",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_ACTIVE_LANE_RULE_v0: ONLY_ONE_ACTIVE_SEAM_CAMPAIGN_PLUS_ONE_THEOREM_GAP_FAMILY_AT_A_TIME",
        "THEORY_RESTART_T42_REMEDIATION_PHASE_P_OPERATOR_PACK_RULE_v0: EXECUTION_REVIEW_MUST_READ_MATRIX_DASHBOARD_SEAM_SLA_ROADMAP_AND_INVENTORY_ONLY",
        "THEORY_RESTART_T42_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t42_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "formal/output/ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0.json",
        "formal/python/tests/test_ws10_t42_redteam_baseline_freeze_gate.py",
        "WS10_REMEDIATION_PHASE_P_T42_STATUS_v0: ACTIVE_REDTEAM_BASELINE_FREEZE_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_P_T42_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_42_DECLARATION_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_P_T42_REPORT_TOOL_v0: formal/python/tools/ws10_t42_redteam_baseline_freeze_report.py",
        "WS10_REMEDIATION_PHASE_P_T42_CHECKPOINT_JSON_v0: formal/output/ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_P_T42_GATE_v0: formal/python/tests/test_ws10_t42_redteam_baseline_freeze_gate.py",
        "WS10_REMEDIATION_PHASE_P_T42_ENTRY_CRITERIA_v0: REFRESH_BASELINE_COUNTS_AND_PIN_FREEZE_RULES_WITHOUT_LIVE_EXECUTION_CHANGE",
        "WS10_REMEDIATION_PHASE_P_T42_PRIMARY_METRICS_v0: THEOREM_GAP_PLUS_SEAM_GAP_PLUS_BLOCKER_NET_DELTA",
        "WS10_REMEDIATION_PHASE_P_T42_RELEASE_SURFACE_RULE_v0: NO_NEW_RELEASE_FAMILY_GROWTH_WITHOUT_RETIREMENT_OR_CANONICAL_BLOCKER_CLOSURE",
        "WS10_REMEDIATION_PHASE_P_T42_GOVERNED_PYTEST_RULE_v0: NO_NEW_GOVERNED_PYTEST_GROWTH_WITHOUT_MANIFEST_JUSTIFIED_RETIREMENT_OR_CANONICAL_BLOCKER_CLOSURE",
        "WS10_REMEDIATION_PHASE_P_T42_ACTIVE_LANE_RULE_v0: ONLY_ONE_ACTIVE_SEAM_CAMPAIGN_PLUS_ONE_THEOREM_GAP_FAMILY_AT_A_TIME",
        "WS10_REMEDIATION_PHASE_P_T42_OPERATOR_PACK_RULE_v0: EXECUTION_REVIEW_MUST_READ_MATRIX_DASHBOARD_SEAM_SLA_ROADMAP_AND_INVENTORY_ONLY",
        "WS10_REMEDIATION_PHASE_P_T42_ADJUDICATION_v0: REDTEAM_BASELINE_FREEZE_AND_EXECUTIVE_METRICS_PINNED_NONLIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase P T42 token(s): " + ", ".join(missing)


def test_ws10_t42_declaration_structure() -> None:
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
    assert "formal/python/tools/ws10_t42_redteam_baseline_freeze_report.py" in text
    assert "formal/output/ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0.json" in text


def test_ws10_t42_checkpoint_matches_tool_output() -> None:
    payload = _json(CHECKPOINT_PATH)
    expected = tool.build_report(
        captured_at_utc=payload.get("captured_at_utc"),
        anchored_commit=payload.get("anchored_commit"),
    )
    assert payload == expected, "T42 checkpoint artifact drifted from generator output."


def test_ws10_t42_checkpoint_semantics() -> None:
    payload = _json(CHECKPOINT_PATH)
    assert payload.get("artifact_id") == "ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0"
    assert payload.get("status") == "ACTIVE_REDTEAM_BASELINE_FREEZE_NONLIVE_v0"
    assert payload.get("anchored_commit") not in {None, "", "UNKNOWN"}

    metrics = payload.get("baseline_metrics", {})
    assert metrics.get("release_surface_file_count", 0) > 0
    assert metrics.get("governance_surface_file_count", 0) > 0
    assert metrics.get("governed_pytests_expected_count") == 341
    assert metrics.get("active_theorem_gap_count") == 7
    assert metrics.get("active_seam_gap_count") == 3
    assert metrics.get("active_parity_drift_count") == 0

    summary = payload.get("summary", {})
    assert summary.get("terminal_outcome") == "REDTEAM_BASELINE_FREEZE_MATERIALIZED"
    assert summary.get("single_executable_seam_reference") == "SEAM-COSMO-SR"
    assert summary.get("blocked_seam_reference") == "SEAM-QM-STAT"
    assert summary.get("external_hold_seam_reference") == "SEAM-QFT-GR"