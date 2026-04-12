from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_q_candidate_discriminative_signal_definition_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_overrides: dict | None = None,
    include_full_signal_shape: bool = True,
) -> None:
    signal_definition = {
        "observable_interface_measurement_named": True,
        "nonmoving_threshold_defined": True,
        "weakly_moving_threshold_defined": True,
        "signal_produced_threshold_defined": False,
        "remaining_phase_o_fields_resolved": False,
    }
    if signal_overrides:
        signal_definition.update(signal_overrides)
    if not include_full_signal_shape:
        signal_definition.pop("remaining_phase_o_fields_resolved")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_p_authorized_candidate_specification_refinement_report": "formal/output/reports/science_phase_p_authorized_candidate_specification_refinement_20260412_v0.json",
                "science_phase_o_authorized_candidate_next_step_selection_report": "formal/output/reports/science_phase_o_authorized_candidate_next_step_selection_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "discriminative_signal_contract": {
                "required_phase_p_outcome": "CANDIDATE_SPECIFICATION_PARTIAL_HOLD_REQUIRES_MORE_DEFINITION",
                "required_phase_p_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_p_packet_authorization": False,
                "required_phase_o_outcome": "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "discriminative_signal_definition": signal_definition,
            },
            "discriminative_signal_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_LAYER_ONLY",
                "allowed_outcomes": [
                    "DISCRIMINATIVE_SIGNAL_DEFINED_AND_LOCKED",
                    "DISCRIMINATIVE_SIGNAL_PARTIAL_HOLD",
                    "CANDIDATE_REQUIRES_DIFFERENT_CANDIDATE_CLASS",
                    "CANDIDATE_WITHDRAWN",
                    "DISCRIMINATIVE_SIGNAL_DEFINITION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_DISCRIMINATIVE_SIGNAL_REPAIR",
                ],
                "default_outcome": "DISCRIMINATIVE_SIGNAL_DEFINITION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_p_outcome: str = "CANDIDATE_SPECIFICATION_PARTIAL_HOLD_REQUIRES_MORE_DEFINITION",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_p_authorized_candidate_specification_refinement_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_p_outcome,
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


def test_reports_discriminative_signal_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "DISCRIMINATIVE_SIGNAL_PARTIAL_HOLD"
    assert report["summary"]["authorize_first_test_packet"] is False


def test_reports_discriminative_signal_defined_and_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={
            "signal_produced_threshold_defined": True,
            "remaining_phase_o_fields_resolved": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "DISCRIMINATIVE_SIGNAL_DEFINED_AND_LOCKED"


def test_reports_hold_pending_discriminative_signal_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_signal_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_DISCRIMINATIVE_SIGNAL_REPAIR"


def test_reports_discriminative_signal_definition_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_p_outcome="AUTHORIZED_CANDIDATE_SPECIFICATION_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "DISCRIMINATIVE_SIGNAL_DEFINITION_EVIDENCE_INCOMPLETE"


def test_reports_candidate_requires_different_candidate_class(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={"observable_interface_measurement_named": False},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CANDIDATE_REQUIRES_DIFFERENT_CANDIDATE_CLASS"