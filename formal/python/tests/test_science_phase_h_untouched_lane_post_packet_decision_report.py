from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_h_untouched_lane_post_packet_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_refinement_path_localized: bool = True,
    different_attack_class_again_required: bool = False,
    path_falsification_evidence_detected: bool = False,
    lane_underdefined_for_further_execution: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_d_untouched_lane_selection_report": "formal/output/reports/science_phase_d_untouched_lane_selection_20260412_v0.json",
                "science_phase_f_untouched_lane_attack_class_reselection_report": "formal/output/reports/science_phase_f_untouched_lane_attack_class_reselection_20260412_v0.json",
                "science_phase_g_untouched_lane_interface_alignment_packet_report": "formal/output/reports/science_phase_g_untouched_lane_interface_alignment_packet_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "decision_policy": {
                "required_phase_d_selection_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "required_phase_f_reselection_outcome": "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK",
                "required_phase_g_packet_outcome": "UNTOUCHED_LANE_VALID_BUT_NONMOVING",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_selected_untouched_lane": "LANE-NEUTRINO-INTERFACE-001",
                "required_selected_attack_class": "neutrino_interface_alignment_boundary_probe",
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
                "selected_attack_class": "neutrino_interface_alignment_boundary_probe",
                "signal_refinement_path_localized": signal_refinement_path_localized,
                "different_attack_class_again_required": different_attack_class_again_required,
                "path_falsification_evidence_detected": path_falsification_evidence_detected,
                "lane_underdefined_for_further_execution": lane_underdefined_for_further_execution,
                "continue_requires_explicit_authorization": True,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "decision_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_H_UNTOUCHED_LANE_POST_PACKET_DECISION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_H_UNTOUCHED_LANE_POST_PACKET_DECISION_LAYER_ONLY",
                "allowed_outcomes": [
                    "UNTOUCHED_LANE_SIGNAL_REFINEMENT_JUSTIFIED",
                    "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS_AGAIN",
                    "UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE",
                    "UNTOUCHED_LANE_PATH_FALSIFIED",
                ],
                "default_outcome": "UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_g_outcome: str = "UNTOUCHED_LANE_VALID_BUT_NONMOVING",
) -> None:
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
        root / "formal" / "output" / "reports" / "science_phase_g_untouched_lane_interface_alignment_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_g_outcome,
                "selected_attack_class": "neutrino_interface_alignment_boundary_probe",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_signal_refinement_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_H_UNTOUCHED_LANE_POST_PACKET_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_SIGNAL_REFINEMENT_JUSTIFIED"


def test_reports_requires_different_attack_class_again(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_H_UNTOUCHED_LANE_POST_PACKET_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_refinement_path_localized=False,
        different_attack_class_again_required=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS_AGAIN"


def test_reports_hold_and_do_not_continue_when_underdefined(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_H_UNTOUCHED_LANE_POST_PACKET_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, lane_underdefined_for_further_execution=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE"


def test_reports_path_falsified_when_evidence_detected(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_H_UNTOUCHED_LANE_POST_PACKET_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, path_falsification_evidence_detected=True)
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
        / "SCIENCE_PHASE_H_UNTOUCHED_LANE_POST_PACKET_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_g_outcome="UNTOUCHED_LANE_SIGNAL_PRODUCED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE"
