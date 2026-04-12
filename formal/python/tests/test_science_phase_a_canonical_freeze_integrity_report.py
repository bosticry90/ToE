from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_a_canonical_freeze_integrity_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_multi_lane_frontier_consolidation_report": "formal/output/reports/science_multi_lane_frontier_consolidation_20260412_v0.json",
                "science_common_failure_modes_synthesis_report": "formal/output/reports/science_common_failure_modes_synthesis_20260412_v0.json",
                "probe_readiness_standard_candidate_report": "formal/output/reports/probe_readiness_standard_candidate_20260412_v0.json",
                "science_restart_mode_selection_report": "formal/output/reports/science_restart_mode_selection_20260412_v0.json",
            },
            "integrity_policy": {
                "required_frontier_outcome": "MULTI_LANE_FRONTIER_CONSOLIDATED_AND_CLOSED",
                "required_synthesis_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED",
                "allowed_probe_candidate_outcomes": [
                    "REQUIRES_RESTART_SELECTION_LAYER",
                    "PROBE_READINESS_STANDARD_CANDIDATE_DRAFTED",
                ],
                "allowed_restart_selection_outcomes": [
                    "RESTART_MODE_SELECTED_POLICY_LANE",
                    "RESTART_MODE_SELECTED_UNTOUCHED_LANE",
                ],
                "blocked_restart_selection_outcomes": [
                    "RESTART_MODE_SELECTION_BLOCKED_CONSUMED_LANE_ALIAS",
                    "RESTART_MODE_SELECTION_EVIDENCE_INCOMPLETE",
                ],
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "integrity_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_LAYER_ONLY",
                "allowed_outcomes": [
                    "PHASE_A_CANONICAL_FREEZE_INTEGRITY_CONFIRMED",
                    "PHASE_A_CANONICAL_FREEZE_INTEGRITY_INCOMPLETE",
                    "PHASE_A_CANONICAL_FREEZE_RESTART_CONTRACT_VIOLATION",
                    "PHASE_A_CANONICAL_FREEZE_HOLD_PENDING_REPAIR",
                ],
                "default_outcome": "PHASE_A_CANONICAL_FREEZE_INTEGRITY_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    frontier_outcome: str = "MULTI_LANE_FRONTIER_CONSOLIDATED_AND_CLOSED",
    selection_outcome: str = "RESTART_MODE_SELECTED_POLICY_LANE",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_multi_lane_frontier_consolidation_20260412_v0.json",
        {"summary": {"terminal_outcome": frontier_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_common_failure_modes_synthesis_20260412_v0.json",
        {"summary": {"terminal_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "probe_readiness_standard_candidate_20260412_v0.json",
        {"summary": {"terminal_outcome": "REQUIRES_RESTART_SELECTION_LAYER"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_mode_selection_20260412_v0.json",
        {"summary": {"terminal_outcome": selection_outcome}},
    )


def test_reports_phase_a_canonical_freeze_integrity_confirmed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PHASE_A_CANONICAL_FREEZE_INTEGRITY_CONFIRMED"


def test_reports_phase_a_canonical_freeze_integrity_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, frontier_outcome="MULTI_LANE_FRONTIER_RECORD_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PHASE_A_CANONICAL_FREEZE_INTEGRITY_INCOMPLETE"


def test_reports_phase_a_canonical_freeze_restart_contract_violation(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, selection_outcome="RESTART_MODE_SELECTION_BLOCKED_CONSUMED_LANE_ALIAS")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PHASE_A_CANONICAL_FREEZE_RESTART_CONTRACT_VIOLATION"


def test_reports_phase_a_canonical_freeze_hold_pending_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_PHASE_A_CANONICAL_FREEZE_INTEGRITY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, selection_outcome="UNKNOWN_SELECTION_STATE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PHASE_A_CANONICAL_FREEZE_HOLD_PENDING_REPAIR"
