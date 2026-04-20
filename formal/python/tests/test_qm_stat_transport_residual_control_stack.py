from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_transport_residual_packet_report as packet_tool
from formal.python.tools import qm_stat_transport_residual_ruling_report as ruling_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def test_qm_stat_transport_residual_packet_classifies_valid_but_nonmoving(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_TRANSPORT_RESIDUAL_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "packet_id": "QMSTAT-TR-001",
            "row_id": "ROW-SEAM-QM-STAT-001",
            "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            "required_inputs": {
                "direct_attack_class_packet_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
                "current_target_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                "prior_target_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle10_v0.json",
                "target_gate_path": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
                "trend_report": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
                "closure_map_report": "formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
            },
            "movement_policy": {
                "success_rule": "SEAM_INTEGRATION_GAP_DELTA_LT_0_OR_THEOREM_GAP_DELTA_LT_0_OR_TARGET_ROW_SUCCESS_INCREMENT_GT_0_OR_BLOCKER_TOKEN_CHANGE_TRUE",
                "failure_rule": "ALL_MOVEMENT_SIGNALS_FALSE",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
                "immediate_ruling_required": True,
            },
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
            "single_bounded_target": {"row_id": "ROW-SEAM-QM-STAT-001"},
        },
    )
    _write_json(
        reports_dir / "governance_blocker_trend_window_20260410_v0.json",
        {
            "blocker_counts": {
                "prior": {"SEAM_INTEGRATION_GAP": 3, "THEOREM_GAP": 7},
                "current": {"SEAM_INTEGRATION_GAP": 3, "THEOREM_GAP": 7},
            }
        },
    )
    _write_json(
        reports_dir / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {"objective_quality": {"inputs": {"row_outcome_counts": {"ROW-PILLAR-QM-001": {"success": 0}}}}},
    )
    _write_json(
        reports_dir / "physics_progress_ledger_v0.json",
        {"actual_blocker_state_change": "NO_DELTA_DETECTED_ROUTE_TO_REWORK"},
    )
    _write_json(
        reports_dir / "governance_blocker_closure_map_20260410_v0.json",
        {
            "mappings": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "owning_lane": "QM_STAT_CYCLE11",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                }
            ]
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle10_v0.json",
        {"adjudication": {"value": "NOT_YET_DISCHARGED"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"seam_id": "SEAM-QM-STAT", "status": "CRITERIA_AND_EIGHTEENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM", "adjudication": {"value": "NOT_YET_DISCHARGED"}},
    )
    _write_text(
        tmp_path / "formal" / "python" / "tests" / "test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
        "def test_placeholder():\n    assert True\n",
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_classification"] == "QM_STAT_TRANSPORT_RESIDUAL_VALID_BUT_NONMOVING"
    assert report["summary"]["seam_integration_gap_delta"] == 0
    assert report["summary"]["theorem_gap_delta"] == 0
    assert report["summary"]["target_row_success_increment_gt_0"] is False
    assert report["summary"]["blocker_token_delta"] == 0


def test_qm_stat_transport_residual_packet_detects_success_increment(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_TRANSPORT_RESIDUAL_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "packet_id": "QMSTAT-TR-001",
            "row_id": "ROW-SEAM-QM-STAT-001",
            "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            "required_inputs": {
                "direct_attack_class_packet_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
                "current_target_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                "prior_target_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle10_v0.json",
                "target_gate_path": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
                "trend_report": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
                "closure_map_report": "formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
            },
            "movement_policy": {
                "success_rule": "SEAM_INTEGRATION_GAP_DELTA_LT_0_OR_THEOREM_GAP_DELTA_LT_0_OR_TARGET_ROW_SUCCESS_INCREMENT_GT_0_OR_BLOCKER_TOKEN_CHANGE_TRUE",
                "failure_rule": "ALL_MOVEMENT_SIGNALS_FALSE",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
                "immediate_ruling_required": True,
            },
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
            "single_bounded_target": {"row_id": "ROW-SEAM-QM-STAT-001"},
        },
    )
    _write_json(
        reports_dir / "governance_blocker_trend_window_20260410_v0.json",
        {
            "blocker_counts": {
                "prior": {"SEAM_INTEGRATION_GAP": 3, "THEOREM_GAP": 7},
                "current": {"SEAM_INTEGRATION_GAP": 2, "THEOREM_GAP": 7},
            }
        },
    )
    _write_json(
        reports_dir / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {"objective_quality": {"inputs": {"row_outcome_counts": {}}}},
    )
    _write_json(
        reports_dir / "physics_progress_ledger_v0.json",
        {"actual_blocker_state_change": "SEAM_INTEGRATION_GAP_REDUCED"},
    )
    _write_json(
        reports_dir / "governance_blocker_closure_map_20260410_v0.json",
        {
            "mappings": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "owning_lane": "QM_STAT_CYCLE11",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                }
            ]
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle10_v0.json",
        {"adjudication": {"value": "NOT_YET_DISCHARGED"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"seam_id": "SEAM-QM-STAT", "status": "CRITERIA_AND_EIGHTEENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM", "adjudication": {"value": "DISCHARGED_v0_BOUNDED"}},
    )
    _write_text(
        tmp_path / "formal" / "python" / "tests" / "test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
        "def test_placeholder():\n    assert True\n",
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_classification"] == "QM_STAT_TRANSPORT_RESIDUAL_MOVED"
    assert report["summary"]["seam_integration_gap_delta"] == -1
    assert report["summary"]["target_row_success_increment_gt_0"] is True
    assert report["summary"]["blocker_token_delta"] == 1


def test_qm_stat_transport_residual_packet_ignores_global_progress_token_without_row_local_signal(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_TRANSPORT_RESIDUAL_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "packet_id": "QMSTAT-TR-001",
            "row_id": "ROW-SEAM-QM-STAT-001",
            "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            "required_inputs": {
                "direct_attack_class_packet_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
                "current_target_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                "prior_target_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle10_v0.json",
                "target_gate_path": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
                "trend_report": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
                "closure_map_report": "formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
            },
            "movement_policy": {
                "success_rule": "SEAM_INTEGRATION_GAP_DELTA_LT_0_OR_THEOREM_GAP_DELTA_LT_0_OR_TARGET_ROW_SUCCESS_INCREMENT_GT_0_OR_BLOCKER_TOKEN_CHANGE_TRUE",
                "failure_rule": "ALL_MOVEMENT_SIGNALS_FALSE",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
                "immediate_ruling_required": True,
            },
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
            "single_bounded_target": {"row_id": "ROW-SEAM-QM-STAT-001"},
        },
    )
    _write_json(
        reports_dir / "governance_blocker_trend_window_20260410_v0.json",
        {
            "blocker_counts": {
                "prior": {"SEAM_INTEGRATION_GAP": 3, "THEOREM_GAP": 7},
                "current": {"SEAM_INTEGRATION_GAP": 3, "THEOREM_GAP": 7},
            }
        },
    )
    _write_json(
        reports_dir / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {"objective_quality": {"inputs": {"row_outcome_counts": {}}}},
    )
    _write_json(
        reports_dir / "physics_progress_ledger_v0.json",
        {"actual_blocker_state_change": "NEGATIVE_DELTA_DETECTED"},
    )
    _write_json(
        reports_dir / "governance_blocker_closure_map_20260410_v0.json",
        {
            "mappings": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "owning_lane": "QM_STAT_CYCLE11",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                }
            ]
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle10_v0.json",
        {"adjudication": {"value": "NOT_YET_DISCHARGED"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {
            "seam_id": "SEAM-QM-STAT",
            "status": "CRITERIA_AND_EIGHTEENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
            "adjudication": {"value": "NOT_YET_DISCHARGED"},
        },
    )
    _write_text(
        tmp_path / "formal" / "python" / "tests" / "test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
        "def test_placeholder():\n    assert True\n",
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_classification"] == "QM_STAT_TRANSPORT_RESIDUAL_VALID_BUT_NONMOVING"
    assert report["summary"]["blocker_token_delta"] == 0
    assert report["summary"]["next_action"] == "EMIT_QM_STAT_TRANSPORT_RESIDUAL_RULING"


def test_qm_stat_transport_residual_ruling_exhausts_nonmoving_single_execution_packet(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(ruling_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_TRANSPORT_RESIDUAL_RULING_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "required_inputs": {
                "qm_stat_transport_residual_packet": "formal/docs/release/QM_STAT_TRANSPORT_RESIDUAL_PACKET_20260411_v0.json",
                "qm_stat_transport_residual_packet_report": "formal/output/reports/qm_stat_transport_residual_packet_20260411_v0.json",
            },
            "ruling_policy": {
                "next_action_if_exhausted": "REVIEW_POST_DIRECT_ATTACK_CLASS_DECISION_AND_DO_NOT_LOOP_QM_STAT",
            },
        },
    )
    _write_json(
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_TRANSPORT_RESIDUAL_PACKET_20260411_v0.json",
        {"row_id": "ROW-SEAM-QM-STAT-001", "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"},
    )
    _write_json(
        reports_dir / "qm_stat_transport_residual_packet_20260411_v0.json",
        {
            "summary": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
                "packet_classification": "QM_STAT_TRANSPORT_RESIDUAL_VALID_BUT_NONMOVING",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
            }
        },
    )

    report = ruling_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["qm_stat_ruling"] == "EXHAUSTED_UNDER_CURRENT_FILTER"
    assert report["summary"]["exclude_from_immediate_reselection"] is True
    assert report["summary"]["next_action"] == "REVIEW_POST_DIRECT_ATTACK_CLASS_DECISION_AND_DO_NOT_LOOP_QM_STAT"
