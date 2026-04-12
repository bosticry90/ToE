from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_e_untouched_lane_post_first_test_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    first_test_local_weakness_identified: bool = False,
    current_attack_class_exhausted: bool = True,
    path_falsification_evidence_detected: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_d_untouched_lane_selection_report": "formal/output/reports/science_phase_d_untouched_lane_selection_20260412_v0.json",
                "science_phase_d_untouched_lane_first_test_packet_report": "formal/output/reports/science_phase_d_untouched_lane_first_test_packet_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "decision_policy": {
                "required_phase_d_selection_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "required_phase_d_first_test_outcome": "UNTOUCHED_LANE_FIRST_TEST_NONDISCRIMINATIVE_HOLD",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_selected_untouched_lane": "LANE-NEUTRINO-INTERFACE-001",
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
                "selected_attack_class": "neutrino_interface_phase_lock_probe",
                "first_test_under_specified": True,
                "first_test_local_weakness_identified": first_test_local_weakness_identified,
                "current_attack_class_exhausted": current_attack_class_exhausted,
                "path_falsification_evidence_detected": path_falsification_evidence_detected,
                "continue_requires_explicit_authorization": True,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "decision_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_LAYER_ONLY",
                "allowed_outcomes": [
                    "UNTOUCHED_LANE_SIGNAL_REFINEMENT_JUSTIFIED",
                    "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS",
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
    first_test_outcome: str = "UNTOUCHED_LANE_FIRST_TEST_NONDISCRIMINATIVE_HOLD",
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
        root / "formal" / "output" / "reports" / "science_phase_d_untouched_lane_first_test_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": first_test_outcome,
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
                "single_attack_class": "neutrino_interface_phase_lock_probe",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_requires_different_attack_class(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_REQUIRES_DIFFERENT_ATTACK_CLASS"


def test_reports_signal_refinement_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        first_test_local_weakness_identified=True,
        current_attack_class_exhausted=False,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_SIGNAL_REFINEMENT_JUSTIFIED"


def test_reports_hold_and_do_not_continue_on_precondition_failure(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, first_test_outcome="UNTOUCHED_LANE_FIRST_TEST_SIGNAL_DETECTED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_HOLD_AND_DO_NOT_CONTINUE"


def test_reports_path_falsified_when_evidence_detected(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_E_UNTOUCHED_LANE_POST_FIRST_TEST_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, path_falsification_evidence_detected=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_PATH_FALSIFIED"
