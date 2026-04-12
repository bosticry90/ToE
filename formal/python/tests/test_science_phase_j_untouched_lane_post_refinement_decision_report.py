from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_j_untouched_lane_post_refinement_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    allow_one_more_bounded_refinement: bool = False,
    different_attack_class_again_required: bool = False,
    path_falsification_evidence_detected: bool = False,
    lane_should_hold_as_valid_but_nonmoving: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_d_untouched_lane_selection_report": "formal/output/reports/science_phase_d_untouched_lane_selection_20260412_v0.json",
                "science_phase_f_untouched_lane_attack_class_reselection_report": "formal/output/reports/science_phase_f_untouched_lane_attack_class_reselection_20260412_v0.json",
                "science_phase_h_untouched_lane_post_packet_decision_report": "formal/output/reports/science_phase_h_untouched_lane_post_packet_decision_20260412_v0.json",
                "science_phase_i_untouched_lane_signal_refinement_packet_report": "formal/output/reports/science_phase_i_untouched_lane_signal_refinement_packet_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "decision_policy": {
                "required_phase_d_selection_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "required_phase_f_reselection_outcome": "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK",
                "required_phase_h_decision_outcome": "UNTOUCHED_LANE_SIGNAL_REFINEMENT_JUSTIFIED",
                "required_phase_i_packet_outcome": "UNTOUCHED_LANE_VALID_BUT_NONMOVING",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_selected_untouched_lane": "LANE-NEUTRINO-INTERFACE-001",
                "required_selected_attack_class": "neutrino_interface_alignment_boundary_probe",
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
                "selected_attack_class": "neutrino_interface_alignment_boundary_probe",
                "allow_one_more_bounded_refinement": allow_one_more_bounded_refinement,
                "different_attack_class_again_required": different_attack_class_again_required,
                "path_falsification_evidence_detected": path_falsification_evidence_detected,
                "lane_should_hold_as_valid_but_nonmoving": lane_should_hold_as_valid_but_nonmoving,
                "continue_requires_explicit_authorization": True,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "decision_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_J_UNTOUCHED_LANE_POST_REFINEMENT_DECISION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_J_UNTOUCHED_LANE_POST_REFINEMENT_DECISION_LAYER_ONLY",
                "allowed_outcomes": [
                    "AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT",
                    "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS_AGAIN",
                    "HOLD_UNTOUCHED_LANE_AS_VALID_BUT_NONMOVING",
                    "UNTOUCHED_LANE_PATH_FALSIFIED",
                ],
                "default_outcome": "HOLD_UNTOUCHED_LANE_AS_VALID_BUT_NONMOVING",
            },
        },
    )


def _seed_inputs(root: Path, *, phase_i_outcome: str = "UNTOUCHED_LANE_VALID_BUT_NONMOVING") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_d_untouched_lane_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "untouched_lane_candidate_id": "LANE-NEUTRINO-INTERFACE-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_f_untouched_lane_attack_class_reselection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK",
                "selected_next_attack_class": "neutrino_interface_alignment_boundary_probe",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_h_untouched_lane_post_packet_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "UNTOUCHED_LANE_SIGNAL_REFINEMENT_JUSTIFIED",
                "selected_attack_class": "neutrino_interface_alignment_boundary_probe",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_i_untouched_lane_signal_refinement_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_i_outcome,
                "selected_attack_class": "neutrino_interface_alignment_boundary_probe",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_hold_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_J_UNTOUCHED_LANE_POST_REFINEMENT_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_UNTOUCHED_LANE_AS_VALID_BUT_NONMOVING"
    assert report["summary"]["continue_authorized"] is False


def test_reports_authorize_one_more_bounded_refinement(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_J_UNTOUCHED_LANE_POST_REFINEMENT_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        allow_one_more_bounded_refinement=True,
        lane_should_hold_as_valid_but_nonmoving=False,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT"
    assert report["summary"]["continue_authorized"] is True


def test_reports_requires_different_attack_class_again(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_J_UNTOUCHED_LANE_POST_REFINEMENT_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        different_attack_class_again_required=True,
        lane_should_hold_as_valid_but_nonmoving=False,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS_AGAIN"
    assert report["summary"]["continue_authorized"] is True


def test_reports_path_falsified_when_evidence_detected(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_J_UNTOUCHED_LANE_POST_REFINEMENT_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        path_falsification_evidence_detected=True,
        lane_should_hold_as_valid_but_nonmoving=False,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_PATH_FALSIFIED"


def test_reports_hold_when_precondition_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_J_UNTOUCHED_LANE_POST_REFINEMENT_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, lane_should_hold_as_valid_but_nonmoving=False)
    _seed_inputs(tmp_path, phase_i_outcome="UNTOUCHED_LANE_SIGNAL_PRODUCED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_UNTOUCHED_LANE_AS_VALID_BUT_NONMOVING"
