from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_d_untouched_lane_selection_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    untouched_lane_candidate_id: str = "LANE-NEUTRINO-INTERFACE-001",
    untouched_lane_non_consumption_proof_declared: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_closed_lane_reopen_eligibility_report": "formal/output/reports/science_closed_lane_reopen_eligibility_20260412_v0.json",
                "probe_readiness_standard_formalization_report": "formal/output/reports/probe_readiness_standard_formalization_20260412_v0.json",
                "science_common_failure_modes_synthesis_report": "formal/output/reports/science_common_failure_modes_synthesis_20260412_v0.json",
            },
            "selection_policy": {
                "required_reopen_eligibility_outcome": "CLOSED_LANE_REOPEN_NONE_ELIGIBLE",
                "required_formalization_outcome": "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED",
                "required_synthesis_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED",
                "consumed_lane_aliases": [
                    "QM-STAT",
                    "GR-ROW-001",
                    "EM-QFT",
                    "SHARED-MODEL-CLASS",
                    "QFT-GR",
                ],
                "untouched_lane_candidate_id": untouched_lane_candidate_id,
                "untouched_lane_non_consumption_proof_declared": untouched_lane_non_consumption_proof_declared,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "selection_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_LAYER_ONLY",
                "allowed_outcomes": [
                    "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                    "UNTOUCHED_LANE_SELECTION_EVIDENCE_INCOMPLETE",
                    "UNTOUCHED_LANE_SELECTION_BLOCKED_CONSUMED_ALIAS",
                    "HOLD_PENDING_UNTOUCHED_CANDIDATE_REPAIR",
                ],
                "default_outcome": "UNTOUCHED_LANE_SELECTION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    reopen_outcome: str = "CLOSED_LANE_REOPEN_NONE_ELIGIBLE",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_reopen_eligibility_20260412_v0.json",
        {"summary": {"terminal_outcome": reopen_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "probe_readiness_standard_formalization_20260412_v0.json",
        {"summary": {"terminal_outcome": "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_common_failure_modes_synthesis_20260412_v0.json",
        {"summary": {"terminal_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED"}},
    )


def test_reports_untouched_lane_selected_for_bounded_first_test(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST"


def test_reports_untouched_lane_selection_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, reopen_outcome="CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_SELECTION_EVIDENCE_INCOMPLETE"


def test_reports_untouched_lane_selection_blocked_consumed_alias(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        untouched_lane_candidate_id="QFT-GR",
        untouched_lane_non_consumption_proof_declared=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_SELECTION_BLOCKED_CONSUMED_ALIAS"


def test_reports_hold_pending_untouched_candidate_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        untouched_lane_candidate_id="LANE-NEUTRINO-INTERFACE-001",
        untouched_lane_non_consumption_proof_declared=False,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_UNTOUCHED_CANDIDATE_REPAIR"
