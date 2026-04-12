from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import architecture_seam_master_action_alignment_attack_class_packet_report as packet_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_alignment_packet_materializes_with_bounded_target(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
            "packet_id": "ASMAA-001",
            "required_inputs": {
                "architecture_level_blocker_diagnosis_packet_report": "formal/output/reports/architecture_level_blocker_diagnosis_packet_20260411_v0.json",
                "science_post_direct_attack_class_decision_report": "formal/output/reports/science_post_direct_attack_class_decision_20260411_v0.json",
                "direct_master_action_residual_transport_attack_class_packet_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
                "qm_stat_transport_residual_ruling_report": "formal/output/reports/qm_stat_transport_residual_ruling_20260411_v0.json",
            },
            "bounded_alignment_scope": {
                "single_alignment_obligation": "SEAM_TO_MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING",
                "single_residual_extraction_interface": "MASTER_ACTION_RESIDUAL_EXTRACTION_INTERFACE_QM_STAT_v0",
                "single_transport_witness": "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0",
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            },
            "alignment_policy": {
                "required_diagnosis_outcome": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE",
                "required_failure_location": "MASTER_ACTION_RESIDUAL_EXTRACTION",
                "required_redesigned_attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
                "required_hold_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
                "default_missing_bridge_object": "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0",
                "default_minimal_upstream_unit": "MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING_UNIT_v0",
                "next_action_if_complete": "EXECUTE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_ONCE",
            },
            "success_failure_measurement": {
                "success_rule": "ALIGNMENT_WITNESS_BOUND_AND_BRIDGE_OBJECT_MATERIALIZED_AND_TARGET_ROW_RECOMPUTE_TRIGGERED",
                "no_loop_failure_rule": "ONE_BOUNDED_ARCHITECTURE_PACKET_ONLY",
            },
        },
    )

    _write_json(
        reports_dir / "architecture_level_blocker_diagnosis_packet_20260411_v0.json",
        {
            "summary": {
                "packet_outcome": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE",
                "blocker_conversion_failure_location": "MASTER_ACTION_RESIDUAL_EXTRACTION",
                "movement_filter_defect_identified": False,
                "upstream_missing_unit_identified": True,
                "selected_redesigned_attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
                "next_action": "MATERIALIZE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET",
            }
        },
    )
    _write_json(
        reports_dir / "science_post_direct_attack_class_decision_20260411_v0.json",
        {
            "summary": {
                "decision": "ESCALATE_TO_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS",
                "local_attack_packet_hold_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
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
            },
            "single_bounded_target": {
                "seam_physics_blocker": "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"
            },
        },
    )
    _write_json(
        reports_dir / "qm_stat_transport_residual_ruling_20260411_v0.json",
        {
            "summary": {
                "qm_stat_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER",
                "row_id": "ROW-SEAM-QM-STAT-001",
            }
        },
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_MATERIALIZED"
    assert (
        report["summary"]["alignment_failure_mode"]
        == "MASTER_ACTION_RESIDUAL_INTERFACE_NOT_BOUND_TO_SEAM_TRANSPORT_WITNESS"
    )
    assert report["summary"]["missing_bridge_object"] == "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0"
    assert (
        report["summary"]["minimal_upstream_unit_to_materialize"]
        == "MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING_UNIT_v0"
    )
    assert report["summary"]["one_bounded_execution_target"]["row_id"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["no-loop failure rule"] == "ONE_BOUNDED_ARCHITECTURE_PACKET_ONLY"


def test_alignment_packet_fails_closed_when_target_row_mismatches(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
            "packet_id": "ASMAA-001",
            "required_inputs": {
                "architecture_level_blocker_diagnosis_packet_report": "formal/output/reports/architecture_level_blocker_diagnosis_packet_20260411_v0.json",
                "science_post_direct_attack_class_decision_report": "formal/output/reports/science_post_direct_attack_class_decision_20260411_v0.json",
                "direct_master_action_residual_transport_attack_class_packet_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
                "qm_stat_transport_residual_ruling_report": "formal/output/reports/qm_stat_transport_residual_ruling_20260411_v0.json",
            },
            "bounded_alignment_scope": {
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            },
            "alignment_policy": {
                "required_diagnosis_outcome": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE",
                "required_failure_location": "MASTER_ACTION_RESIDUAL_EXTRACTION",
                "required_redesigned_attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
                "required_hold_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
            },
            "success_failure_measurement": {
                "success_rule": "ALIGNMENT_WITNESS_BOUND",
                "no_loop_failure_rule": "ONE_BOUNDED_ARCHITECTURE_PACKET_ONLY",
            },
        },
    )

    _write_json(
        reports_dir / "architecture_level_blocker_diagnosis_packet_20260411_v0.json",
        {
            "summary": {
                "packet_outcome": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE",
                "blocker_conversion_failure_location": "MASTER_ACTION_RESIDUAL_EXTRACTION",
                "upstream_missing_unit_identified": True,
                "selected_redesigned_attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
            }
        },
    )
    _write_json(
        reports_dir / "science_post_direct_attack_class_decision_20260411_v0.json",
        {
            "summary": {
                "local_attack_packet_hold_policy": "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
            }
        },
    )
    _write_json(
        reports_dir / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
        {
            "summary": {
                "packet_outcome": "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED",
                "selected_target_row": "ROW-SEAM-QM-STAT-999",
                "selected_target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            },
            "single_bounded_target": {
                "seam_physics_blocker": "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"
            },
        },
    )
    _write_json(
        reports_dir / "qm_stat_transport_residual_ruling_20260411_v0.json",
        {
            "summary": {
                "qm_stat_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER",
                "row_id": "ROW-SEAM-QM-STAT-999",
            }
        },
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_INCOMPLETE"
    assert report["summary"]["alignment_failure_mode"] == "ROW_SEAM_TARGET_ALIGNMENT_MISMATCH"
    assert report["summary"]["next_action"] == "REVIEW_ARCHITECTURE_ALIGNMENT_PACKET_PRECONDITIONS_ONCE"
