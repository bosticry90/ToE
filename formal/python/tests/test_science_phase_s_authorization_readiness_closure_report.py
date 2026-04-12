from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_s_authorization_readiness_closure_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    readiness_overrides: dict | None = None,
    include_full_readiness_shape: bool = True,
) -> None:
    readiness = {
        "remaining_phase_o_fields_resolved": False,
        "authorization_review_ready": False,
        "policy_compliance_bundle_complete": True,
        "candidate_preservation_status_confirmed": True,
        "packet_execution_still_separate": True,
    }
    if readiness_overrides:
        readiness.update(readiness_overrides)
    if not include_full_readiness_shape:
        readiness.pop("packet_execution_still_separate")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_r_signal_produced_threshold_closure_report": "formal/output/reports/science_phase_r_signal_produced_threshold_closure_20260412_v0.json",
                "science_phase_o_authorized_candidate_next_step_selection_report": "formal/output/reports/science_phase_o_authorized_candidate_next_step_selection_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "authorization_readiness_contract": {
                "required_phase_r_outcome": "SIGNAL_THRESHOLD_PARTIAL_HOLD",
                "required_phase_r_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_r_packet_authorization": False,
                "required_phase_o_outcome": "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "authorization_readiness": readiness,
            },
            "authorization_readiness_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_LAYER_ONLY",
                "allowed_outcomes": [
                    "AUTHORIZATION_READINESS_COMPLETE_PACKET_AUTHORIZED",
                    "AUTHORIZATION_READINESS_PARTIAL_HOLD",
                    "CANDIDATE_REQUIRES_HIGHER_LEVEL_POLICY",
                    "CANDIDATE_WITHDRAWN",
                    "AUTHORIZATION_READINESS_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_AUTHORIZATION_READINESS_REPAIR",
                ],
                "default_outcome": "AUTHORIZATION_READINESS_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_r_outcome: str = "SIGNAL_THRESHOLD_PARTIAL_HOLD",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_r_signal_produced_threshold_closure_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_r_outcome,
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


def test_reports_authorization_readiness_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZATION_READINESS_PARTIAL_HOLD"
    assert report["summary"]["authorize_first_test_packet"] is False


def test_reports_authorization_readiness_complete_packet_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        readiness_overrides={
            "remaining_phase_o_fields_resolved": True,
            "authorization_review_ready": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZATION_READINESS_COMPLETE_PACKET_AUTHORIZED"
    assert report["summary"]["authorize_first_test_packet"] is True


def test_reports_hold_pending_authorization_readiness_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_readiness_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_AUTHORIZATION_READINESS_REPAIR"


def test_reports_authorization_readiness_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_r_outcome="SIGNAL_THRESHOLD_CLOSURE_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZATION_READINESS_EVIDENCE_INCOMPLETE"


def test_reports_candidate_requires_higher_level_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        readiness_overrides={"candidate_preservation_status_confirmed": False},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CANDIDATE_REQUIRES_HIGHER_LEVEL_POLICY"