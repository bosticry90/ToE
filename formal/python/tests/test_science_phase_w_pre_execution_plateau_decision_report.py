from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_w_pre_execution_plateau_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_overrides: dict | None = None,
    include_full_signal_shape: bool = True,
) -> None:
    plateau_signals = {
        "authorization_state_changed_since_phase_s": False,
        "distinct_remaining_field_identified": False,
        "residual_blocker_repetition_detected": True,
        "candidate_preservation_status_confirmed": True,
        "policy_escalation_required": False,
    }
    if signal_overrides:
        plateau_signals.update(signal_overrides)
    if not include_full_signal_shape:
        plateau_signals.pop("policy_escalation_required")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_v_execution_guard_binding_closure_report": "formal/output/reports/science_phase_v_execution_guard_binding_closure_20260412_v0.json",
                "science_phase_s_authorization_readiness_closure_report": "formal/output/reports/science_phase_s_authorization_readiness_closure_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "plateau_decision_contract": {
                "required_phase_v_outcome": "EXECUTION_GUARD_BINDING_PARTIAL_HOLD",
                "required_phase_v_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_v_packet_authorization": False,
                "required_phase_s_outcome": "AUTHORIZATION_READINESS_PARTIAL_HOLD",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "plateau_signals": plateau_signals,
            },
            "plateau_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_LAYER_ONLY",
                "allowed_outcomes": [
                    "AUTHORIZE_ONE_FINAL_CLOSURE_TRANCHE",
                    "HOLD_CANDIDATE_AS_NEAR_READY_BUT_NOT_EXECUTABLE",
                    "ESCALATE_TO_HIGHER_LEVEL_POLICY",
                    "WITHDRAW_CANDIDATE_FROM_ACTIVE_PREPARATION",
                    "PRE_EXECUTION_PLATEAU_DECISION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_PRE_EXECUTION_PLATEAU_REPAIR",
                ],
                "default_outcome": "PRE_EXECUTION_PLATEAU_DECISION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_v_outcome: str = "EXECUTION_GUARD_BINDING_PARTIAL_HOLD",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_v_execution_guard_binding_closure_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_v_outcome,
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_s_authorization_readiness_closure_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "AUTHORIZATION_READINESS_PARTIAL_HOLD",
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_hold_candidate_as_near_ready_but_not_executable(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_CANDIDATE_AS_NEAR_READY_BUT_NOT_EXECUTABLE"


def test_reports_authorize_one_final_closure_tranche(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={"distinct_remaining_field_identified": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZE_ONE_FINAL_CLOSURE_TRANCHE"


def test_reports_hold_pending_pre_execution_plateau_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_signal_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_PRE_EXECUTION_PLATEAU_REPAIR"


def test_reports_pre_execution_plateau_decision_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_v_outcome="EXECUTION_GUARD_BINDING_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PRE_EXECUTION_PLATEAU_DECISION_EVIDENCE_INCOMPLETE"


def test_reports_escalate_to_higher_level_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={"policy_escalation_required": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ESCALATE_TO_HIGHER_LEVEL_POLICY"
