from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_p_authorized_candidate_specification_refinement_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    specification_overrides: dict | None = None,
    include_full_specification_shape: bool = True,
) -> None:
    refined_specification = {
        "observable_interface_target_named": True,
        "first_attack_class_admissible_and_named": True,
        "minimum_discriminative_signal_defined": False,
        "anti_alias_evidence_bundle_complete": True,
        "missing_phase_o_fields_resolved": False,
    }
    if specification_overrides:
        refined_specification.update(specification_overrides)
    if not include_full_specification_shape:
        refined_specification.pop("missing_phase_o_fields_resolved")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_o_authorized_candidate_next_step_selection_report": "formal/output/reports/science_phase_o_authorized_candidate_next_step_selection_20260412_v0.json",
                "science_phase_m_selection_policy_activation_criteria_report": "formal/output/reports/science_phase_m_selection_policy_activation_criteria_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "candidate_specification_contract": {
                "required_phase_o_outcome": "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET",
                "required_phase_o_authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "required_phase_o_packet_authorization": False,
                "required_phase_m_outcome": "SELECTION_POLICY_ACTIVATION_CRITERIA_DEFINED_AND_LOCKED",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "refined_specification": refined_specification,
            },
            "candidate_specification_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_LAYER_ONLY",
                "allowed_outcomes": [
                    "CANDIDATE_SPECIFICATION_COMPLETE_PACKET_AUTHORIZATION_JUSTIFIED",
                    "CANDIDATE_SPECIFICATION_PARTIAL_HOLD_REQUIRES_MORE_DEFINITION",
                    "CANDIDATE_REQUIRES_DIFFERENT_CANDIDATE_CLASS",
                    "CANDIDATE_WITHDRAWN",
                    "AUTHORIZED_CANDIDATE_SPECIFICATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_AUTHORIZED_CANDIDATE_SPECIFICATION_REPAIR",
                ],
                "default_outcome": "AUTHORIZED_CANDIDATE_SPECIFICATION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_o_outcome: str = "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_o_authorized_candidate_next_step_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_o_outcome,
                "authorized_lane_id": "LANE-THERMAL-BOUNDARY-001",
                "authorize_first_test_packet": False,
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


def test_reports_candidate_specification_partial_hold_requires_more_definition(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CANDIDATE_SPECIFICATION_PARTIAL_HOLD_REQUIRES_MORE_DEFINITION"
    assert report["summary"]["authorize_first_test_packet"] is False


def test_reports_candidate_specification_complete_packet_authorization_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        specification_overrides={
            "minimum_discriminative_signal_defined": True,
            "missing_phase_o_fields_resolved": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CANDIDATE_SPECIFICATION_COMPLETE_PACKET_AUTHORIZATION_JUSTIFIED"
    assert report["summary"]["authorize_first_test_packet"] is True


def test_reports_hold_pending_authorized_candidate_specification_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_specification_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_AUTHORIZED_CANDIDATE_SPECIFICATION_REPAIR"


def test_reports_authorized_candidate_specification_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_o_outcome="AUTHORIZED_CANDIDATE_SELECTION_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZED_CANDIDATE_SPECIFICATION_EVIDENCE_INCOMPLETE"


def test_reports_candidate_withdrawn(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        specification_overrides={"anti_alias_evidence_bundle_complete": False},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CANDIDATE_WITHDRAWN"