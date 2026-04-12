from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_r_signal_produced_threshold_closure_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    closure_overrides: dict | None = None,
    include_full_closure_shape: bool = True,
) -> None:
    closure = {
        "signal_produced_threshold_defined": True,
        "weakly_moving_vs_signal_produced_separation_defined": True,
        "remaining_phase_o_fields_resolved": False,
        "threshold_measurement_mapping_complete": True,
        "authorization_review_ready": False,
    }
    if closure_overrides:
        closure.update(closure_overrides)
    if not include_full_closure_shape:
        closure.pop("authorization_review_ready")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_q_candidate_discriminative_signal_definition_report": "formal/output/reports/science_phase_q_candidate_discriminative_signal_definition_20260412_v0.json",
                "science_phase_p_authorized_candidate_specification_refinement_report": "formal/output/reports/science_phase_p_authorized_candidate_specification_refinement_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "signal_threshold_contract": {
                "required_phase_q_outcome": "DISCRIMINATIVE_SIGNAL_PARTIAL_HOLD",
                "required_phase_q_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_q_packet_authorization": False,
                "required_phase_p_outcome": "CANDIDATE_SPECIFICATION_PARTIAL_HOLD_REQUIRES_MORE_DEFINITION",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "signal_threshold_closure": closure,
            },
            "signal_threshold_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_R_SIGNAL_PRODUCED_THRESHOLD_CLOSURE_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_R_SIGNAL_PRODUCED_THRESHOLD_CLOSURE_LAYER_ONLY",
                "allowed_outcomes": [
                    "SIGNAL_PRODUCED_THRESHOLD_DEFINED_AND_LOCKED",
                    "SIGNAL_THRESHOLD_PARTIAL_HOLD",
                    "CANDIDATE_REQUIRES_DIFFERENT_CANDIDATE_CLASS",
                    "CANDIDATE_WITHDRAWN",
                    "SIGNAL_THRESHOLD_CLOSURE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_SIGNAL_THRESHOLD_REPAIR",
                ],
                "default_outcome": "SIGNAL_THRESHOLD_CLOSURE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_q_outcome: str = "DISCRIMINATIVE_SIGNAL_PARTIAL_HOLD",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_q_candidate_discriminative_signal_definition_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_q_outcome,
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_p_authorized_candidate_specification_refinement_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "CANDIDATE_SPECIFICATION_PARTIAL_HOLD_REQUIRES_MORE_DEFINITION",
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_signal_threshold_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_R_SIGNAL_PRODUCED_THRESHOLD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SIGNAL_THRESHOLD_PARTIAL_HOLD"
    assert report["summary"]["authorize_first_test_packet"] is False


def test_reports_signal_produced_threshold_defined_and_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_R_SIGNAL_PRODUCED_THRESHOLD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        closure_overrides={
            "remaining_phase_o_fields_resolved": True,
            "authorization_review_ready": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SIGNAL_PRODUCED_THRESHOLD_DEFINED_AND_LOCKED"


def test_reports_hold_pending_signal_threshold_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_R_SIGNAL_PRODUCED_THRESHOLD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_closure_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_SIGNAL_THRESHOLD_REPAIR"


def test_reports_signal_threshold_closure_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_R_SIGNAL_PRODUCED_THRESHOLD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_q_outcome="DISCRIMINATIVE_SIGNAL_DEFINITION_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SIGNAL_THRESHOLD_CLOSURE_EVIDENCE_INCOMPLETE"


def test_reports_candidate_withdrawn(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_R_SIGNAL_PRODUCED_THRESHOLD_CLOSURE_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        closure_overrides={"threshold_measurement_mapping_complete": False},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CANDIDATE_WITHDRAWN"