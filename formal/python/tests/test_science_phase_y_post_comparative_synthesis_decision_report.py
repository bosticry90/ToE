from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_y_post_comparative_synthesis_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_overrides: dict | None = None,
    include_full_signal_shape: bool = True,
) -> None:
    decision_signals = {
        "revise_higher_level_policy_for_near_ready_lanes": False,
        "wait_for_stronger_candidate_class": True,
        "open_new_meta_selection_lane": False,
        "maintain_current_governed_stop_state": False,
        "force_policy_decision_escalation_now": False,
    }
    if signal_overrides:
        decision_signals.update(signal_overrides)
    if not include_full_signal_shape:
        decision_signals.pop("force_policy_decision_escalation_now")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_x_governed_lane_end_comparative_synthesis_report": "formal/output/reports/science_phase_x_governed_lane_end_comparative_synthesis_20260412_v0.json",
                "science_phase_w_pre_execution_plateau_decision_report": "formal/output/reports/science_phase_w_pre_execution_plateau_decision_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "post_comparative_decision_contract": {
                "required_phase_x_outcome": "GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_COMPLETE",
                "required_thermal_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_thermal_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
                "required_thermal_no_further_closure_authorized": True,
                "required_thermal_packet_authorized": False,
                "required_phase_w_outcome": "HOLD_CANDIDATE_AS_NEAR_READY_BUT_NOT_EXECUTABLE",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "decision_signals": decision_signals,
            },
            "post_comparative_decision_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_LAYER_ONLY",
                "allowed_outcomes": [
                    "REVISE_HIGHER_LEVEL_POLICY_FOR_NEAR_READY_LANES",
                    "WAIT_FOR_STRONGER_CANDIDATE_CLASS",
                    "OPEN_NEW_META_SELECTION_LANE",
                    "MAINTAIN_CURRENT_GOVERNED_STOP_STATE",
                    "POST_COMPARATIVE_DECISION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_COMPARATIVE_DECISION_REPAIR",
                ],
                "default_outcome": "POST_COMPARATIVE_DECISION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_x_outcome: str = "GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_COMPLETE",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_x_governed_lane_end_comparative_synthesis_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_x_outcome,
                "thermal_boundary_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
                "thermal_boundary_no_further_closure_authorized": True,
                "thermal_boundary_packet_authorized": False,
            },
            "governed_lane_end_states": {
                "LANE-THERMAL-BOUNDARY-001": {
                    "classification": "NEAR_READY_BUT_NOT_EXECUTABLE_PRESERVED_INACTIVE"
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_w_pre_execution_plateau_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "HOLD_CANDIDATE_AS_NEAR_READY_BUT_NOT_EXECUTABLE",
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
            }
        },
    )


def test_reports_wait_for_stronger_candidate_class(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "WAIT_FOR_STRONGER_CANDIDATE_CLASS"


def test_reports_revise_higher_level_policy_for_near_ready_lanes(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={
            "revise_higher_level_policy_for_near_ready_lanes": True,
            "wait_for_stronger_candidate_class": False,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REVISE_HIGHER_LEVEL_POLICY_FOR_NEAR_READY_LANES"


def test_reports_open_new_meta_selection_lane(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={
            "wait_for_stronger_candidate_class": False,
            "open_new_meta_selection_lane": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "OPEN_NEW_META_SELECTION_LANE"


def test_reports_maintain_current_governed_stop_state(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={
            "wait_for_stronger_candidate_class": False,
            "maintain_current_governed_stop_state": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "MAINTAIN_CURRENT_GOVERNED_STOP_STATE"


def test_reports_hold_pending_post_comparative_decision_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_signal_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_POST_COMPARATIVE_DECISION_REPAIR"


def test_reports_post_comparative_decision_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_x_outcome="GOVERNED_LANE_END_SYNTHESIS_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "POST_COMPARATIVE_DECISION_EVIDENCE_INCOMPLETE"
