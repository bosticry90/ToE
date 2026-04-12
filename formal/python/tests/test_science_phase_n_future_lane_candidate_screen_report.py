from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_n_future_lane_candidate_screen_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    phase_m_authorize_packet_required: bool = False,
    authorize_two_candidates: bool = False,
) -> None:
    candidate_lanes = [
        {
            "lane_id": "LANE-THERMAL-BOUNDARY-001",
            "discriminativity_prerequisites_satisfied": True,
            "attack_class_admissibility_satisfied": True,
            "observable_interface_specificity_satisfied": True,
            "anti_alias_confidence_satisfied": True,
            "closed_lane_alias_risk": "LOW",
            "authorization_decision": "AUTHORIZE",
        },
        {
            "lane_id": "LANE-GEOMETRIC-PHASE-001",
            "discriminativity_prerequisites_satisfied": True,
            "attack_class_admissibility_satisfied": False,
            "observable_interface_specificity_satisfied": True,
            "anti_alias_confidence_satisfied": True,
            "closed_lane_alias_risk": "MEDIUM",
            "authorization_decision": "DENY",
        },
    ]
    if authorize_two_candidates:
        candidate_lanes[1] = {
            "lane_id": "LANE-GEOMETRIC-PHASE-001",
            "discriminativity_prerequisites_satisfied": True,
            "attack_class_admissibility_satisfied": True,
            "observable_interface_specificity_satisfied": True,
            "anti_alias_confidence_satisfied": True,
            "closed_lane_alias_risk": "LOW",
            "authorization_decision": "AUTHORIZE",
        }

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_m_selection_policy_activation_criteria_report": "formal/output/reports/science_phase_m_selection_policy_activation_criteria_20260412_v0.json",
                "science_phase_l_higher_level_selection_policy_report": "formal/output/reports/science_phase_l_higher_level_selection_policy_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "candidate_screen_contract": {
                "required_phase_m_outcome": "SELECTION_POLICY_ACTIVATION_CRITERIA_DEFINED_AND_LOCKED",
                "required_phase_m_authorize_packet": phase_m_authorize_packet_required,
                "required_phase_l_outcome": "HIGHER_LEVEL_SELECTION_POLICY_DEFINED_AND_LOCKED",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "authorize_at_most_one_candidate": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "candidate_lanes": candidate_lanes,
            },
            "candidate_screen_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_LAYER_ONLY",
                "allowed_outcomes": [
                    "FUTURE_LANE_CANDIDATE_SCREEN_COMPLETE_ONE_AUTHORIZED",
                    "FUTURE_LANE_CANDIDATE_SCREEN_COMPLETE_NONE_AUTHORIZED",
                    "FUTURE_LANE_CANDIDATE_SCREEN_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_FUTURE_LANE_SCREEN_REPAIR",
                ],
                "default_outcome": "FUTURE_LANE_CANDIDATE_SCREEN_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_m_outcome: str = "SELECTION_POLICY_ACTIVATION_CRITERIA_DEFINED_AND_LOCKED",
    phase_m_authorize_packet: bool = False,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_m_selection_policy_activation_criteria_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_m_outcome,
                "authorize_new_untouched_lane_packet": phase_m_authorize_packet,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_l_higher_level_selection_policy_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "HIGHER_LEVEL_SELECTION_POLICY_DEFINED_AND_LOCKED",
                "resume_mode": "HIGHER_LEVEL_SELECTION_POLICY_LANE",
                "authorize_new_untouched_lane_packet": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_future_lane_candidate_screen_complete_one_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "FUTURE_LANE_CANDIDATE_SCREEN_COMPLETE_ONE_AUTHORIZED"
    assert report["summary"]["authorized_lane_id"] == "LANE-THERMAL-BOUNDARY-001"
    assert report["summary"]["authorize_new_untouched_lane_packet"] is False


def test_reports_future_lane_candidate_screen_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_m_outcome="SELECTION_POLICY_ACTIVATION_CRITERIA_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "FUTURE_LANE_CANDIDATE_SCREEN_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_future_lane_screen_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_20260412_v0.json"
    )
    _write_declaration(declaration_path, authorize_two_candidates=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_FUTURE_LANE_SCREEN_REPAIR"


def test_reports_future_lane_candidate_screen_evidence_incomplete_on_phase_m_authorization_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_20260412_v0.json"
    )
    _write_declaration(declaration_path, phase_m_authorize_packet_required=False)
    _seed_inputs(tmp_path, phase_m_authorize_packet=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "FUTURE_LANE_CANDIDATE_SCREEN_EVIDENCE_INCOMPLETE"