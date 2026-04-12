from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_u_execution_guard_authorization_ready_closure_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    closure_overrides: dict | None = None,
    include_full_closure_shape: bool = True,
) -> None:
    closure_fields = {
        "execution_guard_binding_closed": False,
        "authorization_review_ready": False,
        "packet_execution_still_separate": True,
        "policy_escalation_required": False,
    }
    if closure_overrides:
        closure_fields.update(closure_overrides)
    if not include_full_closure_shape:
        closure_fields.pop("policy_escalation_required")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_t_residual_authorization_field_closure_report": "formal/output/reports/science_phase_t_residual_authorization_field_closure_20260412_v0.json",
                "science_phase_o_authorized_candidate_next_step_selection_report": "formal/output/reports/science_phase_o_authorized_candidate_next_step_selection_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "execution_guard_authorization_contract": {
                "required_phase_t_outcome": "RESIDUAL_FIELD_PARTIAL_HOLD",
                "required_phase_t_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_t_packet_authorization": False,
                "required_phase_o_outcome": "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "closure_fields": closure_fields,
            },
            "execution_guard_authorization_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_U_EXECUTION_GUARD_AUTHORIZATION_READY_CLOSURE_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_U_EXECUTION_GUARD_AUTHORIZATION_READY_CLOSURE_LAYER_ONLY",
                "allowed_outcomes": [
                    "AUTHORIZATION_REVIEW_READY_AND_PACKET_AUTHORIZED",
                    "EXECUTION_GUARD_PARTIAL_HOLD",
                    "REQUIRES_HIGHER_LEVEL_POLICY",
                    "CANDIDATE_WITHDRAWN",
                    "EXECUTION_GUARD_AUTHORIZATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_EXECUTION_GUARD_REPAIR",
                ],
                "default_outcome": "EXECUTION_GUARD_AUTHORIZATION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_t_outcome: str = "RESIDUAL_FIELD_PARTIAL_HOLD",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_t_residual_authorization_field_closure_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_t_outcome,
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_o_authorized_candidate_next_step_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET",
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_execution_guard_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_U_EXECUTION_GUARD_AUTHORIZATION_READY_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EXECUTION_GUARD_PARTIAL_HOLD"
    assert report["summary"]["authorize_first_test_packet"] is False


def test_reports_authorization_review_ready_and_packet_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_U_EXECUTION_GUARD_AUTHORIZATION_READY_CLOSURE_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        closure_overrides={
            "execution_guard_binding_closed": True,
            "authorization_review_ready": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZATION_REVIEW_READY_AND_PACKET_AUTHORIZED"
    assert report["summary"]["authorize_first_test_packet"] is True


def test_reports_hold_pending_execution_guard_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_U_EXECUTION_GUARD_AUTHORIZATION_READY_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_closure_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_EXECUTION_GUARD_REPAIR"


def test_reports_execution_guard_authorization_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_U_EXECUTION_GUARD_AUTHORIZATION_READY_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_t_outcome="RESIDUAL_FIELD_CLOSURE_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EXECUTION_GUARD_AUTHORIZATION_EVIDENCE_INCOMPLETE"


def test_reports_requires_higher_level_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_U_EXECUTION_GUARD_AUTHORIZATION_READY_CLOSURE_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        closure_overrides={"policy_escalation_required": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REQUIRES_HIGHER_LEVEL_POLICY"
