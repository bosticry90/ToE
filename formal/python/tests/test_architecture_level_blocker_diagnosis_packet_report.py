from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import architecture_level_blocker_diagnosis_packet_report as packet_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_architecture_level_packet_completes_on_clean_escalation(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "attack_class": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS",
            "packet_id": "ALBD-001",
            "required_inputs": {
                "science_post_direct_attack_class_decision_report": "formal/output/reports/science_post_direct_attack_class_decision_20260411_v0.json",
                "proof_debt_program_exhaustion_decision_report": "formal/output/reports/proof_debt_program_exhaustion_decision_20260411_v0.json",
                "qm_blocker_moving_ruling_report": "formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json",
                "qm_stat_transport_residual_ruling_report": "formal/output/reports/qm_stat_transport_residual_ruling_20260411_v0.json",
                "direct_master_action_residual_transport_attack_class_packet_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
            },
            "diagnosis_questions": [{"question_id": "Q1", "prompt": "Where is blocker conversion actually failing?"}],
            "diagnosis_policy": {
                "required_prior_nonmoving_attack_classes": [
                    "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
                    "QM_BLOCKER_MOVING_TRANCHE",
                    "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
                ],
                "local_attack_hold_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
                "default_blocker_conversion_failure_location": "MASTER_ACTION_RESIDUAL_EXTRACTION",
                "default_upstream_missing_unit": "ARCHITECTURE_LEVEL_BLOCKER_CONVERSION_UNIT",
                "default_selected_redesigned_attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
                "next_action_if_complete": "MATERIALIZE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET",
            },
        },
    )

    _write_json(
        reports_dir / "science_post_direct_attack_class_decision_20260411_v0.json",
        {
            "summary": {
                "decision": "ESCALATE_TO_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS",
                "filter_revision_status": "NO_SPECIFIC_FILTER_DEFECT_IDENTIFIED",
                "selected_next_attack_class": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS",
                "local_attack_packet_hold_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
                "next_action": "MATERIALIZE_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET",
            }
        },
    )
    _write_json(
        reports_dir / "proof_debt_program_exhaustion_decision_20260411_v0.json",
        {"summary": {"program_state": "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"}},
    )
    _write_json(
        reports_dir / "qm_blocker_moving_ruling_20260411_v0.json",
        {"summary": {"qm_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER"}},
    )
    _write_json(
        reports_dir / "qm_stat_transport_residual_ruling_20260411_v0.json",
        {
            "summary": {
                "qm_stat_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER",
                "row_id": "ROW-SEAM-QM-STAT-001",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            }
        },
    )
    _write_json(
        reports_dir / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
        {
            "summary": {
                "packet_outcome": "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED",
                "selected_target_row": "ROW-SEAM-QM-STAT-001",
                "selected_target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            }
        },
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE"
    assert report["summary"]["blocker_conversion_failure_location"] == "MASTER_ACTION_RESIDUAL_EXTRACTION"
    assert report["summary"]["movement_filter_defect_identified"] is False
    assert report["summary"]["upstream_missing_unit_identified"] is True
    assert (
        report["summary"]["selected_redesigned_attack_class"]
        == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS"
    )
    assert (
        report["summary"]["next_action"]
        == "MATERIALIZE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET"
    )


def test_architecture_level_packet_fails_closed_without_architecture_decision(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "attack_class": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS",
            "packet_id": "ALBD-001",
            "required_inputs": {
                "science_post_direct_attack_class_decision_report": "formal/output/reports/science_post_direct_attack_class_decision_20260411_v0.json",
                "proof_debt_program_exhaustion_decision_report": "formal/output/reports/proof_debt_program_exhaustion_decision_20260411_v0.json",
                "qm_blocker_moving_ruling_report": "formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json",
                "qm_stat_transport_residual_ruling_report": "formal/output/reports/qm_stat_transport_residual_ruling_20260411_v0.json",
                "direct_master_action_residual_transport_attack_class_packet_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
            },
            "diagnosis_policy": {
                "required_prior_nonmoving_attack_classes": [
                    "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
                    "QM_BLOCKER_MOVING_TRANCHE",
                    "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
                ],
                "local_attack_hold_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
                "default_blocker_conversion_failure_location": "MASTER_ACTION_RESIDUAL_EXTRACTION",
            },
        },
    )

    _write_json(
        reports_dir / "science_post_direct_attack_class_decision_20260411_v0.json",
        {
            "summary": {
                "decision": "PROGRAM_POSTURE_REVIEW_REQUIRED",
                "filter_revision_status": "NO_SPECIFIC_FILTER_DEFECT_IDENTIFIED",
                "selected_next_attack_class": None,
                "local_attack_packet_hold_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
                "next_action": "REVIEW_BLOCKER_MOVING_UNIT_DEFINITION_AND_PROGRAM_POSTURE_ONCE",
            }
        },
    )
    _write_json(
        reports_dir / "proof_debt_program_exhaustion_decision_20260411_v0.json",
        {"summary": {"program_state": "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"}},
    )
    _write_json(
        reports_dir / "qm_blocker_moving_ruling_20260411_v0.json",
        {"summary": {"qm_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER"}},
    )
    _write_json(
        reports_dir / "qm_stat_transport_residual_ruling_20260411_v0.json",
        {"summary": {"qm_stat_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER", "row_id": "ROW-SEAM-QM-STAT-001"}},
    )
    _write_json(
        reports_dir / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
        {
            "summary": {
                "packet_outcome": "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED",
                "selected_target_row": "ROW-SEAM-QM-STAT-001",
            }
        },
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_INCOMPLETE"
    assert report["summary"]["next_action"] == "REVIEW_ARCHITECTURE_LEVEL_DIAGNOSIS_PRECONDITIONS_ONCE"
