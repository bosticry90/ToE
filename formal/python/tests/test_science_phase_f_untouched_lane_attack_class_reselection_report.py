from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_f_untouched_lane_attack_class_reselection_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_refinement_supported: bool = False,
    interface_alignment_supported: bool = True,
    different_target_subseam_supported: bool = False,
    lane_underdefined_for_next_packet: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_d_untouched_lane_selection_report": "formal/output/reports/science_phase_d_untouched_lane_selection_20260412_v0.json",
                "science_phase_d_untouched_lane_first_test_packet_report": "formal/output/reports/science_phase_d_untouched_lane_first_test_packet_20260412_v0.json",
                "science_phase_e_untouched_lane_post_first_test_decision_report": "formal/output/reports/science_phase_e_untouched_lane_post_first_test_decision_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "reselection_policy": {
                "required_phase_d_selection_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "required_phase_d_first_test_outcome": "UNTOUCHED_LANE_FIRST_TEST_NONDISCRIMINATIVE_HOLD",
                "required_phase_e_decision_outcome": "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_selected_untouched_lane": "LANE-NEUTRINO-INTERFACE-001",
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
                "previous_attack_class": "neutrino_interface_phase_lock_probe",
                "signal_refinement_supported": signal_refinement_supported,
                "interface_alignment_supported": interface_alignment_supported,
                "different_target_subseam_supported": different_target_subseam_supported,
                "lane_underdefined_for_next_packet": lane_underdefined_for_next_packet,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "reselection_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_LAYER_ONLY",
                "allowed_outcomes": [
                    "UNTOUCHED_LANE_SIGNAL_REFINEMENT_ATTACK",
                    "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK",
                    "UNTOUCHED_LANE_DIFFERENT_TARGET_SUBSEAM_ATTACK",
                    "HOLD_UNTOUCHED_LANE_AND_STOP",
                ],
                "default_outcome": "HOLD_UNTOUCHED_LANE_AND_STOP",
            },
        },
    )


def _seed_inputs(root: Path, *, phase_e_outcome: str = "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS") -> None:
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
        root / "formal" / "output" / "reports" / "science_phase_d_untouched_lane_first_test_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "UNTOUCHED_LANE_FIRST_TEST_NONDISCRIMINATIVE_HOLD",
                "single_attack_class": "neutrino_interface_phase_lock_probe",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_e_untouched_lane_post_first_test_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": phase_e_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_interface_alignment_attack(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK"


def test_reports_signal_refinement_attack(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_refinement_supported=True,
        interface_alignment_supported=False,
        different_target_subseam_supported=False,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_SIGNAL_REFINEMENT_ATTACK"


def test_reports_different_target_subseam_attack(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_refinement_supported=False,
        interface_alignment_supported=False,
        different_target_subseam_supported=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_DIFFERENT_TARGET_SUBSEAM_ATTACK"


def test_reports_hold_when_lane_underdefined(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, lane_underdefined_for_next_packet=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_UNTOUCHED_LANE_AND_STOP"


def test_reports_hold_when_precondition_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_e_outcome="UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_UNTOUCHED_LANE_AND_STOP"
