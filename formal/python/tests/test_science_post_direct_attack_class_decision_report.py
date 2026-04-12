from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_post_direct_attack_class_decision_report as decision_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path, *, specific_filter_defect_identified: bool, bounded_filter_revision_packet: str | None) -> None:
    _write_json(
        path,
        {
            "current_attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
            "required_inputs": {
                "science_global_completion_baseline_report": "formal/output/reports/science_global_completion_baseline_20260411_v0.json",
                "proof_debt_program_exhaustion_decision_report": "formal/output/reports/proof_debt_program_exhaustion_decision_20260411_v0.json",
                "qm_blocker_moving_ruling_report": "formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json",
                "direct_master_action_residual_transport_attack_class_packet_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
                "qm_stat_transport_residual_ruling_report": "formal/output/reports/qm_stat_transport_residual_ruling_20260411_v0.json",
            },
            "candidate_routes": [],
            "decision_policy": {
                "specific_filter_defect_identified": specific_filter_defect_identified,
                "specific_filter_defect_note": None,
                "bounded_filter_revision_packet": bounded_filter_revision_packet,
                "minimum_distinct_nonmoving_attack_classes": 3,
                "required_nonmoving_attack_classes": [
                    "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
                    "QM_BLOCKER_MOVING_TRANCHE",
                    "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
                ],
                "architecture_level_selected_attack_class": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS",
                "architecture_level_next_action": "MATERIALIZE_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET",
                "program_posture_review_next_action": "REVIEW_BLOCKER_MOVING_UNIT_DEFINITION_AND_PROGRAM_POSTURE_ONCE",
                "no_further_local_attack_packets_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
            },
        },
    )


def _write_minimum_inputs(reports_dir: Path) -> None:
    _write_json(
        reports_dir / "science_global_completion_baseline_20260411_v0.json",
        {"completion_assessment": {"science_global_complete": False, "global_objective_complete": False}},
    )
    _write_json(
        reports_dir / "proof_debt_program_exhaustion_decision_20260411_v0.json",
        {
            "summary": {
                "program_state": "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER",
                "decision": "ESCALATE_TO_NEXT_ATTACK_CLASS",
            }
        },
    )
    _write_json(
        reports_dir / "qm_blocker_moving_ruling_20260411_v0.json",
        {
            "summary": {
                "qm_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER",
                "row_id": "ROW-PILLAR-QM-001",
                "subtarget_id": "QM_PACKET04_THRESHOLD_ALIGNMENT_SUBPROBLEM_v0",
            }
        },
    )
    _write_json(
        reports_dir / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
        {
            "attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
            "failure_synthesis": {
                "prior_classes": [
                    {"attack_class": "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN", "movement_observed": False},
                    {"attack_class": "QM_BLOCKER_MOVING_TRANCHE", "movement_observed": False},
                    {"attack_class": "BROADER_SEAM_PACKAGE_REDESIGN", "movement_observed": False},
                ]
            },
            "summary": {
                "packet_outcome": "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED",
                "selected_attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
                "selected_target_row": "ROW-SEAM-QM-STAT-001",
                "selected_target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            },
        },
    )


def test_post_direct_attack_decision_escalates_to_architecture_level_diagnosis(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(decision_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_DIRECT_ATTACK_CLASS_DECISION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        specific_filter_defect_identified=False,
        bounded_filter_revision_packet=None,
    )
    _write_minimum_inputs(reports_dir)
    _write_json(
        reports_dir / "qm_stat_transport_residual_ruling_20260411_v0.json",
        {
            "summary": {
                "qm_stat_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER",
                "packet_classification": "QM_STAT_TRANSPORT_RESIDUAL_VALID_BUT_NONMOVING",
                "row_id": "ROW-SEAM-QM-STAT-001",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            }
        },
    )

    report = decision_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["decision"] == "ESCALATE_TO_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS"
    assert report["summary"]["selected_next_attack_class"] == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS"
    assert report["summary"]["next_action"] == "MATERIALIZE_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET"
    assert report["summary"]["distinct_nonmoving_attack_class_count"] == 3


def test_post_direct_attack_decision_prefers_bounded_filter_revision_when_declared(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(decision_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_DIRECT_ATTACK_CLASS_DECISION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        specific_filter_defect_identified=True,
        bounded_filter_revision_packet="FILTER_REVISION_PACKET_20260411_v0",
    )
    _write_minimum_inputs(reports_dir)
    _write_json(
        reports_dir / "qm_stat_transport_residual_ruling_20260411_v0.json",
        {"summary": {"qm_stat_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER"}},
    )

    report = decision_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["decision"] == "FILTER_REVISION_JUSTIFIED_AND_BOUNDED"
    assert report["summary"]["selected_next_attack_class"] is None
    assert report["summary"]["next_action"] == "EXECUTE_FILTER_REVISION_PACKET_ONCE"


def test_post_direct_attack_decision_requires_program_posture_review_when_current_attack_is_not_exhausted(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(decision_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_DIRECT_ATTACK_CLASS_DECISION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        specific_filter_defect_identified=False,
        bounded_filter_revision_packet=None,
    )
    _write_minimum_inputs(reports_dir)
    _write_json(
        reports_dir / "qm_stat_transport_residual_ruling_20260411_v0.json",
        {"summary": {"qm_stat_ruling": "RULING_INCOMPLETE"}},
    )

    report = decision_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["decision"] == "PROGRAM_POSTURE_REVIEW_REQUIRED"
    assert report["summary"]["selected_next_attack_class"] is None
    assert report["summary"]["next_action"] == "REVIEW_BLOCKER_MOVING_UNIT_DEFINITION_AND_PROGRAM_POSTURE_ONCE"
