from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_external_path_signal_packet_report as packet_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_seam": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "lane": "QM_STAT_CYCLE11",
                "blocker_class": "SEAM_INTEGRATION_GAP",
            },
            "required_inputs": {
                "discovery_engine_scoring_routing_review_report": "formal/output/reports/discovery_engine_scoring_routing_review_20260411_v0.json",
                "discovery_engine_review_checkpoint_report": "formal/output/reports/discovery_engine_review_checkpoint_20260411_v0.json",
                "discovery_priority_queue_report": "formal/output/reports/discovery_priority_queue_report_20260411_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
                "qm_stat_discovery_interpretation_report": "formal/output/reports/qm_stat_discovery_interpretation_report_20260411_v0.json",
                "qm_stat_discovery_numerical_probe_execution_report": "formal/output/reports/qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json",
                "qm_stat_discovery_post_derivation_probe_decision_report": "formal/output/reports/qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
            },
            "baseline_comparator": {
                "comparator_id": "QM_STAT_SINGLE_BASELINE_COMPARATOR_v0",
                "comparator_kind": "STANDARD_BASELINE_OR_COMPETING_PATH_NUMERICAL_REFERENCE",
                "comparator_policy": "ONE_DECLARED_BASELINE_COMPARATOR_ONLY",
                "current_status": "DECLARED_VIA_REQUIRED_REPORT",
            },
            "candidate_external_path_signal": {
                "signal_id": "QM_STAT_EXTERNAL_PATH_SIGNAL_v0",
                "signal_definition": "Produce EXTERNALLY_COMPARABLE or NUMERICAL_PROBE_READY.",
                "supported_interpretations": ["EXTERNALLY_COMPARABLE", "NUMERICAL_PROBE_READY"],
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "EXTERNAL_PATH_SIGNAL_PRODUCED",
                    "PATH_FALSIFIED",
                    "INTERNAL_ONLY_REMAINS",
                ],
                "success_rule": "AT_LEAST_ONE_EXTERNALLY_COMPARABLE_DISCRIMINATOR_CANDIDATE_PRODUCED",
                "failure_rule": "NO_EXTERNAL_SEPARATION_BEYOND_INTERNAL_ONLY_DISCRIMINATION",
                "path_falsification_rule": "PATH_FALSIFICATION_OBSERVED_TRUE",
                "no_loop_rule": "ONE_EXTERNAL_PATH_SIGNAL_PACKET_ONLY",
            },
            "selection_policy": {
                "require_hold_state": True,
                "require_target_to_remain_top_ranked": True,
                "require_absent_external_path_signal": True,
            },
        },
    )


def _write_common_inputs(reports_dir: Path) -> None:
    _write_json(
        reports_dir / "discovery_engine_scoring_routing_review_20260411_v0.json",
        {
            "summary": {
                "selected_review_disposition": "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY",
                "credible_external_path_signal_present": False,
            }
        },
    )
    _write_json(
        reports_dir / "discovery_engine_review_checkpoint_20260411_v0.json",
        {"summary": {"selected_expansion_decision": "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT"}},
    )
    _write_json(
        reports_dir / "discovery_priority_queue_report_20260411_v0.json",
        {"summary": {"top_rank_row": "ROW-SEAM-QM-STAT-001"}},
    )
    _write_json(
        reports_dir / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "candidate_mapping_status": "MOMENT_PARITY_SIGNATURE_ONLY_NOT_YET_RL10_OBSERVABLE_READY",
            }
        },
    )
    _write_json(
        reports_dir / "qm_stat_discovery_interpretation_report_20260411_v0.json",
        {"summary": {"target_row": "ROW-SEAM-QM-STAT-001", "interpretation": "INTERNAL_DISCRIMINATIVE_ONLY"}},
    )
    _write_json(
        reports_dir / "qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json",
        {"summary": {"probe_signal": "PROBE_NONDISCRIMINATIVE"}},
    )
    _write_json(
        reports_dir / "qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
        {"summary": {"post_cycle_decision": "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE"}},
    )


def test_qm_stat_external_path_packet_materializes_from_current_hold_state(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir)

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_MATERIALIZED"
    assert report["summary"]["selected_target_row"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["baseline_comparator_status"] == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
    assert report["summary"]["next_action"] == "EXECUTE_ONE_QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_ONCE"


def test_qm_stat_external_path_packet_detects_when_external_signal_is_already_present(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir)
    _write_json(
        reports_dir / "discovery_engine_scoring_routing_review_20260411_v0.json",
        {
            "summary": {
                "selected_review_disposition": "REOPEN_ONE_BOUNDED_LANE_EXPANSION",
                "credible_external_path_signal_present": True,
            }
        },
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "QM_STAT_EXTERNAL_PATH_SIGNAL_ALREADY_PRESENT"
    assert report["summary"]["next_action"] == "REOPEN_DISCOVERY_EXPANSION_REVIEW_ONCE"


def test_qm_stat_external_path_packet_fails_closed_when_target_alignment_breaks(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir)
    _write_json(
        reports_dir / "discovery_priority_queue_report_20260411_v0.json",
        {"summary": {"top_rank_row": "ROW-SEAM-QFT-GR-001"}},
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_INCOMPLETE"
    assert report["summary"]["next_action"] == "REPAIR_QM_STAT_EXTERNALIZATION_INPUTS_ONCE"


def test_qm_stat_external_path_packet_fails_closed_without_declared_single_baseline_comparator(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir)
    _write_json(
        reports_dir / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {"summary": {"comparator_status": "COMPARATOR_DECLARATION_INCOMPLETE"}},
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_INCOMPLETE"
    assert report["summary"]["next_action"] == "REPAIR_QM_STAT_EXTERNALIZATION_INPUTS_ONCE"
