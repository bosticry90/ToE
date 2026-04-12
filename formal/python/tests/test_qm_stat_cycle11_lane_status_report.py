from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_cycle11_lane_status_report as status_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_lane": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "lane": "QM_STAT_CYCLE11",
            },
            "required_inputs": {
                "qm_stat_discovery_post_derivation_probe_decision_report": "formal/output/reports/qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
                "qm_stat_rl10_observable_mapping_review_report": "formal/output/reports/qm_stat_rl10_observable_mapping_review_20260411_v0.json",
                "qm_stat_rl10_interface_transformation_report": "formal/output/reports/qm_stat_rl10_interface_transformation_20260411_v0.json",
                "qm_stat_rl10_sigma_db_transformation_report": "formal/output/reports/qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
                "qm_stat_transition_dynamics_feasibility_review_report": "formal/output/reports/qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
                "discovery_engine_scoring_routing_review_report": "formal/output/reports/discovery_engine_scoring_routing_review_20260411_v0.json",
            },
            "status_contract": {
                "allowed_externalization_status": [
                    "OUT_OF_SCOPE_UNDER_CYCLE11",
                    "INCOMPLETE_BUT_STILL_IN_SCOPE_UNDER_CYCLE11",
                    "PATH_FALSIFIED",
                ],
                "allowed_internal_lane_status": ["RETAINED", "RETIRED"],
                "no_loop_rule": "ONE_QM_STAT_CYCLE11_LANE_STATUS_SYNTHESIS_ONLY",
                "routing_implication_rule": "IF_EXTERNALIZATION_STATUS_IS_OUT_OF_SCOPE_UNDER_CYCLE11_THEN_QM_STAT_CANNOT_SATISFY_CURRENT_EXTERNAL_PATH_REOPEN_CONDITION",
            },
        },
    )


def _write_common_inputs(root: Path) -> None:
    reports = root / "formal" / "output" / "reports"
    _write_json(
        reports / "qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
        {"summary": {"post_cycle_decision": "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE"}},
    )
    _write_json(
        reports / "qm_stat_rl10_observable_mapping_review_20260411_v0.json",
        {"summary": {"mapping_review_outcome": "RL10_MAPPING_NOT_YET_DEFINED"}},
    )
    _write_json(
        reports / "qm_stat_rl10_interface_transformation_20260411_v0.json",
        {"summary": {"transformation_outcome": "RL10_INTERFACE_PARTIAL_HOLD"}},
    )
    _write_json(
        reports / "qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
        {"summary": {"transformation_outcome": "SIGMA_DB_INTERFACE_PARTIAL_HOLD"}},
    )
    _write_json(
        reports / "discovery_engine_scoring_routing_review_20260411_v0.json",
        {
            "summary": {
                "lane_expansion_reopen_condition": "CREDIBLE_EXTERNAL_PATH_SIGNAL_PRESENT_AND_RANK3_OVER_RANK4_GAP_GE_3_AND_DISCOVERY_REVIEW_HOLD_RESOLVED_ONCE"
            }
        },
    )


def test_lane_status_reports_retained_but_out_of_scope_when_transition_dynamics_review_closes_cycle11(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(status_tool, "REPO_ROOT", tmp_path)

    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_LANE_STATUS_20260411_v0.json"
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
        {"summary": {"review_outcome": "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE"}},
    )

    report = status_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["internal_lane_status"] == "RETAINED"
    assert report["summary"]["externalization_status"] == "OUT_OF_SCOPE_UNDER_CYCLE11"
    assert report["summary"]["eligible_for_external_path_reopen_signal_under_cycle11"] is False
    assert report["summary"]["routing_implication"] == "DO_NOT_COUNT_QM_STAT_AS_CURRENT_EXTERNAL_PATH_SIGNAL"


def test_lane_status_reports_path_falsified_when_feasibility_review_falsifies_route(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(status_tool, "REPO_ROOT", tmp_path)

    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_LANE_STATUS_20260411_v0.json"
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
        {"summary": {"review_outcome": "QM_STAT_RL10_EXTERNALIZATION_PATH_FALSIFIED"}},
    )

    report = status_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["externalization_status"] == "PATH_FALSIFIED"
    assert report["summary"]["eligible_for_external_path_reopen_signal_under_cycle11"] is False


def test_lane_status_reports_in_scope_when_transition_extension_is_justified(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(status_tool, "REPO_ROOT", tmp_path)

    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_LANE_STATUS_20260411_v0.json"
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
        {"summary": {"review_outcome": "TRANSITION_DYNAMICS_EXTENSION_JUSTIFIED"}},
    )

    report = status_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["externalization_status"] == "INCOMPLETE_BUT_STILL_IN_SCOPE_UNDER_CYCLE11"
    assert report["summary"]["eligible_for_external_path_reopen_signal_under_cycle11"] is True
