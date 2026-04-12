from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_post_architecture_alignment_decision_report as decision_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    movement_metric_defect_identified: bool,
    bounded_metric_revision_packet: str | None,
    architecture_unit_selection_defect_identified: bool,
    bounded_unit_selection_revision_packet: str | None,
) -> None:
    _write_json(
        path,
        {
            "current_attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
            "required_inputs": {
                "architecture_seam_master_action_alignment_ruling_report": "formal/output/reports/architecture_seam_master_action_alignment_ruling_20260411_v0.json",
                "architecture_seam_master_action_alignment_packet_execution_report": "formal/output/reports/architecture_seam_master_action_alignment_packet_execution_20260411_v0.json",
                "architecture_level_blocker_diagnosis_packet_report": "formal/output/reports/architecture_level_blocker_diagnosis_packet_20260411_v0.json",
            },
            "candidate_routes": [],
            "decision_policy": {
                "movement_metric_defect_identified": movement_metric_defect_identified,
                "movement_metric_defect_note": None,
                "bounded_metric_revision_packet": bounded_metric_revision_packet,
                "architecture_unit_selection_defect_identified": architecture_unit_selection_defect_identified,
                "architecture_unit_selection_defect_note": None,
                "bounded_unit_selection_revision_packet": bounded_unit_selection_revision_packet,
                "program_posture_review_next_action": "MATERIALIZE_PROGRAM_POSTURE_REVIEW_PACKET",
                "no_loop_rule": "ONE_POST_ARCHITECTURE_DECISION_ONLY",
                "no_further_architecture_attack_packets_policy": "NO_FURTHER_ARCHITECTURE_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED",
            },
        },
    )


def _write_minimum_inputs(reports_dir: Path) -> None:
    _write_json(
        reports_dir / "architecture_seam_master_action_alignment_ruling_20260411_v0.json",
        {
            "summary": {
                "alignment_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER",
                "execution_classification": "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING",
                "next_action": "REVIEW_POST_ARCHITECTURE_ALIGNMENT_DECISION_AND_DO_NOT_LOOP_ALIGNMENT_PACKET",
            }
        },
    )
    _write_json(
        reports_dir / "architecture_seam_master_action_alignment_packet_execution_20260411_v0.json",
        {
            "summary": {
                "execution_classification": "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING",
                "bridge_object_materialized": True,
                "alignment_witness_bound": True,
                "target_row_recompute_triggered": True,
                "blocker_movement_signal_true": False,
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
                "next_action": "EMIT_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_RULING",
            }
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


def test_post_architecture_alignment_decision_defaults_to_program_posture_review(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(decision_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_ARCHITECTURE_ALIGNMENT_DECISION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        movement_metric_defect_identified=False,
        bounded_metric_revision_packet=None,
        architecture_unit_selection_defect_identified=False,
        bounded_unit_selection_revision_packet=None,
    )
    _write_minimum_inputs(reports_dir)

    report = decision_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["post_architecture_decision"] == "PROGRAM_POSTURE_REVIEW_REQUIRED"
    assert report["summary"]["specific_defect_identified"] is False
    assert report["summary"]["defect_scope"] is None
    assert report["summary"]["selected_next_program_mode"] == "PROGRAM_POSTURE_REVIEW"
    assert report["summary"]["next_action"] == "MATERIALIZE_PROGRAM_POSTURE_REVIEW_PACKET"


def test_post_architecture_alignment_decision_routes_to_metric_defect_when_bounded(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(decision_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_ARCHITECTURE_ALIGNMENT_DECISION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        movement_metric_defect_identified=True,
        bounded_metric_revision_packet="MOVEMENT_METRIC_REVISION_PACKET_20260411_v0",
        architecture_unit_selection_defect_identified=False,
        bounded_unit_selection_revision_packet=None,
    )
    _write_minimum_inputs(reports_dir)

    report = decision_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["post_architecture_decision"] == "MOVEMENT_METRIC_DEFECT_IDENTIFIED_AND_BOUNDED"
    assert report["summary"]["specific_defect_identified"] is True
    assert report["summary"]["defect_scope"] == "MOVEMENT_METRIC"
    assert report["summary"]["selected_next_program_mode"] == "MOVEMENT_METRIC_REVISION"
    assert report["summary"]["next_action"] == "EXECUTE_MOVEMENT_METRIC_REVISION_PACKET_ONCE"
