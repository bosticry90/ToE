from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_x_governed_lane_end_comparative_synthesis_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_overrides: dict | None = None,
    include_full_signal_shape: bool = True,
) -> None:
    signals = {
        "lane_end_family_complete": True,
        "thermal_lane_marked_preserved_inactive": True,
        "thermal_lane_further_closure_prohibited": True,
        "thermal_lane_packet_prohibited": True,
        "project_level_synthesis_only": True,
        "policy_revision_evaluation_required": True,
        "force_policy_escalation_now": False,
    }
    if signal_overrides:
        signals.update(signal_overrides)
    if not include_full_signal_shape:
        signals.pop("force_policy_escalation_now")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_w_pre_execution_plateau_decision_report": "formal/output/reports/science_phase_w_pre_execution_plateau_decision_20260412_v0.json",
                "science_phase_j_untouched_lane_post_refinement_decision_report": "formal/output/reports/science_phase_j_untouched_lane_post_refinement_decision_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "governed_lane_end_synthesis_contract": {
                "required_phase_w_outcome": "HOLD_CANDIDATE_AS_NEAR_READY_BUT_NOT_EXECUTABLE",
                "required_phase_w_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_w_packet_authorization": False,
                "required_phase_j_outcome": "HOLD_UNTOUCHED_LANE_AS_VALID_BUT_NONMOVING",
                "required_phase_j_target_lane": "LANE-NEUTRINO-INTERFACE-001",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_closed_lane_ids": [
                    "QM-STAT",
                    "GR-ROW-001",
                    "EM-QFT",
                    "SHARED-MODEL-CLASS",
                    "QFT-GR",
                ],
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "synthesis_signals": signals,
            },
            "governed_lane_end_synthesis_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_LAYER_ONLY",
                "allowed_outcomes": [
                    "GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_COMPLETE",
                    "ESCALATE_TO_HIGHER_LEVEL_POLICY_FOR_FUTURE_CANDIDATE_SELECTION",
                    "GOVERNED_LANE_END_SYNTHESIS_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_GOVERNED_LANE_END_SYNTHESIS_REPAIR",
                ],
                "default_outcome": "GOVERNED_LANE_END_SYNTHESIS_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_w_outcome: str = "HOLD_CANDIDATE_AS_NEAR_READY_BUT_NOT_EXECUTABLE",
    include_full_closed_lane_coverage: bool = True,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_w_pre_execution_plateau_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_w_outcome,
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_j_untouched_lane_post_refinement_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "HOLD_UNTOUCHED_LANE_AS_VALID_BUT_NONMOVING",
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
            }
        },
    )

    reasons = {
        "QM-STAT": "External-validation policy prerequisites remain incomplete under formalized standard.",
        "GR-ROW-001": "Current architecture still requires a new seam or model-class structure before probe-ready progression.",
        "EM-QFT": "Current interface alignment route still requires a new seam or model-class structure before probe-ready progression.",
        "SHARED-MODEL-CLASS": "Lane remains externally comparable but not probe-ready under formalized comparator/repeatability thresholds.",
        "QFT-GR": "Lane remains externally comparable but not probe-ready under formalized comparator/repeatability thresholds.",
    }
    if not include_full_closed_lane_coverage:
        reasons.pop("QFT-GR")

    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
            },
            "closed_lane_non_reopen_reasons": reasons,
        },
    )


def test_reports_governed_lane_end_comparative_synthesis_complete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_COMPLETE"
    assert report["summary"]["thermal_boundary_no_further_closure_authorized"] is True
    assert report["summary"]["thermal_boundary_packet_authorized"] is False


def test_reports_escalate_to_higher_level_policy_for_future_candidate_selection(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={"force_policy_escalation_now": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["terminal_outcome"]
        == "ESCALATE_TO_HIGHER_LEVEL_POLICY_FOR_FUTURE_CANDIDATE_SELECTION"
    )


def test_reports_hold_pending_governed_lane_end_synthesis_repair(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_signal_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_GOVERNED_LANE_END_SYNTHESIS_REPAIR"


def test_reports_governed_lane_end_synthesis_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_X_GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        phase_w_outcome="PRE_EXECUTION_PLATEAU_DECISION_EVIDENCE_INCOMPLETE",
        include_full_closed_lane_coverage=False,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GOVERNED_LANE_END_SYNTHESIS_EVIDENCE_INCOMPLETE"
