from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_t_residual_authorization_field_closure_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    residual_overrides: dict | None = None,
    include_full_residual_shape: bool = True,
) -> None:
    residual = {
        "phase_o_field_observable_contract_closed": True,
        "phase_o_field_attack_class_contract_closed": True,
        "phase_o_field_execution_guard_binding_closed": False,
        "authorization_review_ready": False,
        "packet_execution_still_separate": True,
        "policy_escalation_required": False,
    }
    if residual_overrides:
        residual.update(residual_overrides)
    if not include_full_residual_shape:
        residual.pop("policy_escalation_required")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_s_authorization_readiness_closure_report": "formal/output/reports/science_phase_s_authorization_readiness_closure_20260412_v0.json",
                "science_phase_o_authorized_candidate_next_step_selection_report": "formal/output/reports/science_phase_o_authorized_candidate_next_step_selection_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "residual_field_contract": {
                "required_phase_s_outcome": "AUTHORIZATION_READINESS_PARTIAL_HOLD",
                "required_phase_s_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_s_packet_authorization": False,
                "required_phase_o_outcome": "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "residual_authorization_fields": residual,
            },
            "residual_field_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_T_RESIDUAL_AUTHORIZATION_FIELD_CLOSURE_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_T_RESIDUAL_AUTHORIZATION_FIELD_CLOSURE_LAYER_ONLY",
                "allowed_outcomes": [
                    "AUTHORIZATION_REVIEW_READY_AND_PACKET_AUTHORIZED",
                    "RESIDUAL_FIELD_PARTIAL_HOLD",
                    "REQUIRES_HIGHER_LEVEL_POLICY",
                    "CANDIDATE_WITHDRAWN",
                    "RESIDUAL_FIELD_CLOSURE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RESIDUAL_FIELD_REPAIR",
                ],
                "default_outcome": "RESIDUAL_FIELD_CLOSURE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_s_outcome: str = "AUTHORIZATION_READINESS_PARTIAL_HOLD",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_s_authorization_readiness_closure_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_s_outcome,
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


def test_reports_residual_field_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_T_RESIDUAL_AUTHORIZATION_FIELD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RESIDUAL_FIELD_PARTIAL_HOLD"
    assert report["summary"]["authorize_first_test_packet"] is False


def test_reports_authorization_review_ready_and_packet_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_T_RESIDUAL_AUTHORIZATION_FIELD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        residual_overrides={
            "phase_o_field_execution_guard_binding_closed": True,
            "authorization_review_ready": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZATION_REVIEW_READY_AND_PACKET_AUTHORIZED"
    assert report["summary"]["authorize_first_test_packet"] is True


def test_reports_hold_pending_residual_field_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_T_RESIDUAL_AUTHORIZATION_FIELD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_residual_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RESIDUAL_FIELD_REPAIR"


def test_reports_residual_field_closure_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_T_RESIDUAL_AUTHORIZATION_FIELD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_s_outcome="AUTHORIZATION_READINESS_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RESIDUAL_FIELD_CLOSURE_EVIDENCE_INCOMPLETE"


def test_reports_requires_higher_level_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_T_RESIDUAL_AUTHORIZATION_FIELD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        residual_overrides={"policy_escalation_required": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REQUIRES_HIGHER_LEVEL_POLICY"