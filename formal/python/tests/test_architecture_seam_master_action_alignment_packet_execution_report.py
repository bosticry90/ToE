from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import architecture_seam_master_action_alignment_packet_execution_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_execution_report_materializes_bridge_and_witness(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_EXECUTION_20260411_v0.json"
    )
    reports = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "required_inputs": {
                "architecture_seam_master_action_alignment_attack_class_packet_report": "formal/output/reports/architecture_seam_master_action_alignment_attack_class_packet_20260411_v0.json",
                "trend_report": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
            },
            "materialization_targets": {
                "bridge_object_id": "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0",
                "minimal_upstream_unit_id": "MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING_UNIT_v0",
                "alignment_witness_id": "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0",
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            },
            "movement_policy": {
                "success_rule": "X",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
            },
        },
    )

    _write_json(
        reports / "architecture_seam_master_action_alignment_attack_class_packet_20260411_v0.json",
        {
            "summary": {
                "packet_outcome": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_MATERIALIZED",
                "one_bounded_execution_target": {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
                },
            }
        },
    )
    _write_json(
        reports / "governance_blocker_trend_window_20260410_v0.json",
        {
            "blocker_counts": {
                "prior": {"THEOREM_GAP": 5, "SEAM_INTEGRATION_GAP": 4},
                "current": {"THEOREM_GAP": 5, "SEAM_INTEGRATION_GAP": 4},
            }
        },
    )
    _write_json(
        reports / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {
            "objective_quality": {
                "inputs": {"row_outcome_counts": {"ROW-SEAM-QM-STAT-001": {"success": 0}}}
            }
        },
    )
    _write_json(
        reports / "physics_progress_ledger_v0.json",
        {"actual_blocker_state_change": "NO_DELTA_DETECTED_ROUTE_TO_REWORK"},
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["execution_classification"] == "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING"
    assert report["summary"]["bridge_object_materialized"] is True
    assert report["summary"]["alignment_witness_bound"] is True
    assert report["summary"]["target_row_recompute_triggered"] is True
