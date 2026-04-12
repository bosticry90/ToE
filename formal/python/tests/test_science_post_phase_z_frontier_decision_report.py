from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_post_phase_z_frontier_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_overrides: dict | None = None,
    include_full_signal_shape: bool = True,
) -> None:
    frontier_signals = {
        "preserve_current_governed_stop_state": True,
        "revise_higher_level_policy": False,
        "open_candidate_generation_framework_redesign": False,
        "wait_for_external_evidence_inputs": False,
        "force_policy_escalation_now": False,
    }
    if signal_overrides:
        frontier_signals.update(signal_overrides)
    if not include_full_signal_shape:
        frontier_signals.pop("force_policy_escalation_now")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_z_stronger_candidate_class_discovery_report": "formal/output/reports/science_phase_z_stronger_candidate_class_discovery_20260412_v0.json",
                "science_phase_y_post_comparative_synthesis_decision_report": "formal/output/reports/science_phase_y_post_comparative_synthesis_decision_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "post_phase_z_frontier_decision_contract": {
                "required_phase_z_outcome": "NO_STRONGER_CANDIDATE_CLASS_IDENTIFIED_YET",
                "required_phase_y_outcome": "WAIT_FOR_STRONGER_CANDIDATE_CLASS",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_thermal_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
                "required_thermal_no_further_closure_authorized": True,
                "required_thermal_packet_authorized": False,
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "frontier_signals": frontier_signals,
            },
            "post_phase_z_frontier_decision_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_LAYER_ONLY",
                "allowed_outcomes": [
                    "PRESERVE_CURRENT_GOVERNED_STOP_STATE",
                    "REVISE_HIGHER_LEVEL_POLICY",
                    "OPEN_CANDIDATE_GENERATION_FRAMEWORK_REDESIGN",
                    "WAIT_FOR_EXTERNAL_EVIDENCE_INPUTS",
                    "POST_PHASE_Z_FRONTIER_DECISION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PHASE_Z_FRONTIER_DECISION_REPAIR",
                ],
                "default_outcome": "POST_PHASE_Z_FRONTIER_DECISION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_z_outcome: str = "NO_STRONGER_CANDIDATE_CLASS_IDENTIFIED_YET",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_z_stronger_candidate_class_discovery_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_z_outcome,
                "thermal_boundary_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
                "thermal_boundary_no_further_closure_authorized": True,
                "thermal_boundary_packet_authorized": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_y_post_comparative_synthesis_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "WAIT_FOR_STRONGER_CANDIDATE_CLASS",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_preserve_current_governed_stop_state(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PRESERVE_CURRENT_GOVERNED_STOP_STATE"


def test_reports_revise_higher_level_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={
            "preserve_current_governed_stop_state": False,
            "revise_higher_level_policy": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REVISE_HIGHER_LEVEL_POLICY"


def test_reports_open_candidate_generation_framework_redesign(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={
            "preserve_current_governed_stop_state": False,
            "open_candidate_generation_framework_redesign": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "OPEN_CANDIDATE_GENERATION_FRAMEWORK_REDESIGN"


def test_reports_wait_for_external_evidence_inputs(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={
            "preserve_current_governed_stop_state": False,
            "wait_for_external_evidence_inputs": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "WAIT_FOR_EXTERNAL_EVIDENCE_INPUTS"


def test_reports_hold_pending_post_phase_z_frontier_decision_repair(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_signal_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_POST_PHASE_Z_FRONTIER_DECISION_REPAIR"


def test_reports_post_phase_z_frontier_decision_evidence_incomplete(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_z_outcome="STRONGER_CANDIDATE_CLASS_DISCOVERY_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "POST_PHASE_Z_FRONTIER_DECISION_EVIDENCE_INCOMPLETE"
