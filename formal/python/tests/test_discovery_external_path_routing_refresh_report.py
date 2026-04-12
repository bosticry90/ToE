from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import discovery_external_path_routing_refresh_report as refresh_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "discovery_priority_queue_report": "formal/output/reports/discovery_priority_queue_report_20260411_v0.json",
                "discovery_engine_scoring_routing_review_report": "formal/output/reports/discovery_engine_scoring_routing_review_20260411_v0.json",
                "qm_stat_cycle11_lane_status_report": "formal/output/reports/qm_stat_cycle11_lane_status_20260411_v0.json",
                "qft_gr_discovery_interpretation_report": "formal/output/reports/qft_gr_discovery_interpretation_report_20260411_v0.json",
            },
            "refresh_contract": {
                "allowed_outcomes": [
                    "QM_STAT_EXCLUDED_NO_EXTERNAL_PATH_CANDIDATE_REMAINS",
                    "QM_STAT_EXCLUDED_NEXT_EXTERNAL_PATH_CANDIDATE_AVAILABLE",
                    "ROUTING_INPUTS_INCOMPLETE",
                ],
                "no_loop_rule": "ONE_DISCOVERY_EXTERNAL_PATH_ROUTING_REFRESH_ONLY",
                "routing_goal": "CONTINUE_DISCOVERY_ROUTING_WITHOUT_COUNTING_QM_STAT_AS_A_CURRENT_EXTERNAL_PATH_REOPEN_CANDIDATE",
            },
        },
    )


def test_refresh_reports_no_candidate_remains_when_qm_stat_is_excluded_and_qft_gr_is_not_ready(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(refresh_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_EXTERNAL_PATH_ROUTING_REFRESH_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "discovery_priority_queue_report_20260411_v0.json",
        {
            "summary": {"top_rank_row": "ROW-SEAM-QM-STAT-001"},
            "ranked_candidates": [
                {"row_id": "ROW-SEAM-QM-STAT-001", "lane": "QM_STAT_CYCLE11"},
                {"row_id": "ROW-SEAM-QFT-GR-001", "lane": "QFT_GR_REACTIVATION"},
            ],
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "discovery_engine_scoring_routing_review_20260411_v0.json",
        {"summary": {"selected_review_disposition": "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_cycle11_lane_status_20260411_v0.json",
        {
            "summary": {
                "internal_lane_status": "RETAINED",
                "externalization_status": "OUT_OF_SCOPE_UNDER_CYCLE11",
                "eligible_for_external_path_reopen_signal_under_cycle11": False,
            }
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qft_gr_discovery_interpretation_report_20260411_v0.json",
        {"summary": {"interpretation": "INTERNAL_DISCRIMINATIVE_ONLY", "probe_ready": False, "probe_lane_allowed": False}},
    )

    report = refresh_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "QM_STAT_EXCLUDED_NO_EXTERNAL_PATH_CANDIDATE_REMAINS"
    assert report["summary"]["qm_stat_counted_as_current_external_path_candidate"] is False
    assert report["summary"]["remaining_external_path_candidate_count"] == 0


def test_refresh_reports_next_candidate_available_when_qft_gr_is_ready(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(refresh_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_EXTERNAL_PATH_ROUTING_REFRESH_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "discovery_priority_queue_report_20260411_v0.json",
        {
            "summary": {"top_rank_row": "ROW-SEAM-QM-STAT-001"},
            "ranked_candidates": [
                {"row_id": "ROW-SEAM-QM-STAT-001", "lane": "QM_STAT_CYCLE11"},
                {"row_id": "ROW-SEAM-QFT-GR-001", "lane": "QFT_GR_REACTIVATION"},
            ],
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "discovery_engine_scoring_routing_review_20260411_v0.json",
        {"summary": {"selected_review_disposition": "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_cycle11_lane_status_20260411_v0.json",
        {
            "summary": {
                "internal_lane_status": "RETAINED",
                "externalization_status": "OUT_OF_SCOPE_UNDER_CYCLE11",
                "eligible_for_external_path_reopen_signal_under_cycle11": False,
            }
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qft_gr_discovery_interpretation_report_20260411_v0.json",
        {"summary": {"interpretation": "BOUNDED_EXTERNAL_PATH_READY", "probe_ready": True, "probe_lane_allowed": True}},
    )

    report = refresh_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "QM_STAT_EXCLUDED_NEXT_EXTERNAL_PATH_CANDIDATE_AVAILABLE"
    assert report["summary"]["selected_external_path_row_id"] == "ROW-SEAM-QFT-GR-001"
    assert report["summary"]["remaining_external_path_candidate_count"] == 1


def test_refresh_reports_incomplete_when_queue_inputs_are_missing(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(refresh_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_EXTERNAL_PATH_ROUTING_REFRESH_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "discovery_priority_queue_report_20260411_v0.json",
        {"summary": {}, "ranked_candidates": []},
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "discovery_engine_scoring_routing_review_20260411_v0.json",
        {"summary": {}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_cycle11_lane_status_20260411_v0.json",
        {"summary": {"eligible_for_external_path_reopen_signal_under_cycle11": False}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qft_gr_discovery_interpretation_report_20260411_v0.json",
        {"summary": {"probe_ready": False, "probe_lane_allowed": False}},
    )

    report = refresh_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "ROUTING_INPUTS_INCOMPLETE"
