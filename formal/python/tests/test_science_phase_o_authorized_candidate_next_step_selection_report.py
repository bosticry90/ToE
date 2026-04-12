from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_o_authorized_candidate_next_step_selection_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    evidence_overrides: dict | None = None,
    include_full_evidence_shape: bool = True,
) -> None:
    evidence = {
        "phase_m_criteria_satisfied": True,
        "non_aliasing_against_lane_end_family": True,
        "observable_interface_specificity_complete": False,
        "first_attack_class_defined_without_underdefinition": False,
        "risk_of_valid_but_nonmoving_repeat_bounded": False,
    }
    if evidence_overrides:
        evidence.update(evidence_overrides)
    if not include_full_evidence_shape:
        evidence.pop("risk_of_valid_but_nonmoving_repeat_bounded")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_n_future_lane_candidate_screen_report": "formal/output/reports/science_phase_n_future_lane_candidate_screen_20260412_v0.json",
                "science_phase_m_selection_policy_activation_criteria_report": "formal/output/reports/science_phase_m_selection_policy_activation_criteria_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "authorized_candidate_contract": {
                "required_phase_n_outcome": "FUTURE_LANE_CANDIDATE_SCREEN_COMPLETE_ONE_AUTHORIZED",
                "required_phase_n_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_n_packet_authorization": False,
                "required_phase_m_outcome": "SELECTION_POLICY_ACTIVATION_CRITERIA_DEFINED_AND_LOCKED",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "authorized_candidate_evidence": evidence,
            },
            "authorized_candidate_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_LAYER_ONLY",
                "allowed_outcomes": [
                    "AUTHORIZE_LANE_THERMAL_BOUNDARY_FIRST_TEST_PACKET",
                    "REQUIRE_ONE_MORE_CANDIDATE_LEVEL_CLARIFICATION",
                    "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET",
                    "CANDIDATE_PATH_WITHDRAWN",
                    "AUTHORIZED_CANDIDATE_SELECTION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_AUTHORIZED_CANDIDATE_SELECTION_REPAIR",
                ],
                "default_outcome": "AUTHORIZED_CANDIDATE_SELECTION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_n_outcome: str = "FUTURE_LANE_CANDIDATE_SCREEN_COMPLETE_ONE_AUTHORIZED",
    phase_n_authorized_lane_id: str = "LANE-THERMAL-BOUNDARY-001",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_n_future_lane_candidate_screen_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_n_outcome,
                "authorized_lane_id": phase_n_authorized_lane_id,
                "authorize_new_untouched_lane_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_m_selection_policy_activation_criteria_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "SELECTION_POLICY_ACTIVATION_CRITERIA_DEFINED_AND_LOCKED",
                "authorize_new_untouched_lane_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_require_one_more_candidate_level_clarification(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        evidence_overrides={"observable_interface_specificity_complete": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REQUIRE_ONE_MORE_CANDIDATE_LEVEL_CLARIFICATION"
    assert report["summary"]["authorize_first_test_packet"] is False


def test_reports_authorize_lane_thermal_boundary_first_test_packet(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        evidence_overrides={
            "observable_interface_specificity_complete": True,
            "first_attack_class_defined_without_underdefinition": True,
            "risk_of_valid_but_nonmoving_repeat_bounded": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZE_LANE_THERMAL_BOUNDARY_FIRST_TEST_PACKET"
    assert report["summary"]["authorize_first_test_packet"] is True


def test_reports_hold_pending_authorized_candidate_selection_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_evidence_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_AUTHORIZED_CANDIDATE_SELECTION_REPAIR"


def test_reports_authorized_candidate_selection_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_n_outcome="FUTURE_LANE_CANDIDATE_SCREEN_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZED_CANDIDATE_SELECTION_EVIDENCE_INCOMPLETE"


def test_reports_candidate_path_withdrawn(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        evidence_overrides={"non_aliasing_against_lane_end_family": False},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CANDIDATE_PATH_WITHDRAWN"