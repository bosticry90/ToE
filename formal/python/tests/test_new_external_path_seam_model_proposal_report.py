from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import new_external_path_seam_model_proposal_report as proposal_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "discovery_external_path_routing_refresh_report": "formal/output/reports/discovery_external_path_routing_refresh_20260411_v0.json",
                "qm_stat_cycle11_lane_status_report": "formal/output/reports/qm_stat_cycle11_lane_status_20260411_v0.json",
                "qm_stat_transition_dynamics_feasibility_review_report": "formal/output/reports/qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
                "qm_stat_rl10_sigma_db_transformation_report": "formal/output/reports/qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
            },
            "proposal_scope": {
                "proposed_seam_model_class_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM_v0",
                "target_row_family": "ROW-SEAM-QM-STAT-001_SUCCESSOR_CLASS",
                "baseline_comparator_id": "OV-RL-10",
                "missing_external_path_structures": [
                    "DISCRETE_TRANSITION_DYNAMICS_OPERATOR_OR_MARKOV_KERNEL",
                    "BIDIRECTIONAL_TRANSITION_RATES_OR_EQUIVALENT_TRANSITION_MATRIX",
                    "STATIONARY_FLOW_TO_SIGMA_DB_OBSERVABLE_INTERFACE",
                ],
                "non_insertability_claim": "THE_REQUIRED_TRANSITION_STRUCTURE_CANNOT_BE_INSERTED_INTO_QM_STAT_CYCLE11_WITHOUT_EXITING_THE_CURRENT_HIGHER_MOMENT_AUDIT_SCOPE",
                "bounded_first_test_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_v0",
                "bounded_first_test_description": "DECLARE_ONE_DISCRETE_TRANSITION_KERNEL_PLUS_BIDIRECTIONAL_RATE_STRUCTURE_AND_CHECK_SINGLE_BASELINE_OV_RL_10_SIGMA_DB_INTERFACE_COMPATIBILITY_ON_CURRENT_DISCRETE_SUPPORT_ONLY",
            },
            "proposal_contract": {
                "allowed_outcomes": [
                    "NEW_SEAM_MODEL_PROPOSAL_JUSTIFIED",
                    "PROPOSAL_UNDERDEFINED",
                    "NO_NEW_SEAM_MODEL_CLASS_JUSTIFIED_YET",
                ],
                "no_loop_rule": "ONE_NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_ONLY",
                "no_existing_lane_reopen_rule": "DO_NOT_REOPEN_EXISTING_QM_STAT_OR_OTHER_CYCLE11_LANES_FROM_THIS_PROPOSAL",
                "success_rule": "A_SINGLE_NEW_SEAM_MODEL_CLASS_AND_SINGLE_BOUNDED_FIRST_TEST_ARE_BOTH_SPECIFIED_AND_ROOTED_IN_CURRENT_MISSING_EXTERNAL_PATH_STRUCTURE",
            },
        },
    )


def _write_common_inputs(root: Path) -> None:
    reports = root / "formal" / "output" / "reports"
    _write_json(
        reports / "discovery_external_path_routing_refresh_20260411_v0.json",
        {"summary": {"refresh_outcome": "QM_STAT_EXCLUDED_NO_EXTERNAL_PATH_CANDIDATE_REMAINS", "remaining_external_path_candidate_count": 0}},
    )
    _write_json(
        reports / "qm_stat_cycle11_lane_status_20260411_v0.json",
        {"summary": {"externalization_status": "OUT_OF_SCOPE_UNDER_CYCLE11", "internal_lane_status": "RETAINED"}},
    )
    _write_json(
        reports / "qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
        {"summary": {"review_outcome": "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE", "resulting_model_class": "NEW_SEAM_OR_MODEL_CLASS_REQUIRED"}},
    )
    _write_json(
        reports / "qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
        {
            "summary": {
                "sigma_proxy_definable_from_current_qm_stat_surfaces": False,
                "db_residual_definable_from_current_qm_stat_surfaces": False,
                "sigma_proxy_assumptions_required": ["DECLARE_DISCRETE_TRANSITION_DYNAMICS_OPERATOR_OR_MARKOV_KERNEL"],
                "db_residual_assumptions_required": ["DECLARE_BIDIRECTIONAL_TRANSITION_RATES_OR_EQUIVALENT_TRANSITION_MATRIX"],
            }
        },
    )
    _write_json(
        reports / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {"summary": {"comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY", "baseline_id": "OV-RL-10"}},
    )


def test_proposal_reports_justified_when_missing_structure_and_no_current_candidate_are_both_present(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(proposal_tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_20260411_v0.json"
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)

    report = proposal_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["proposal_outcome"] == "NEW_SEAM_MODEL_PROPOSAL_JUSTIFIED"
    assert report["summary"]["proposed_seam_model_class_id"] == "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM_v0"


def test_proposal_reports_underdefined_when_baseline_compatibility_is_missing(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(proposal_tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_20260411_v0.json"
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {"summary": {"comparator_status": "MISSING", "baseline_id": ""}},
    )

    report = proposal_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["proposal_outcome"] == "PROPOSAL_UNDERDEFINED"


def test_proposal_reports_not_justified_yet_when_an_external_candidate_still_exists(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(proposal_tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_20260411_v0.json"
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "discovery_external_path_routing_refresh_20260411_v0.json",
        {"summary": {"refresh_outcome": "QM_STAT_EXCLUDED_NEXT_EXTERNAL_PATH_CANDIDATE_AVAILABLE", "remaining_external_path_candidate_count": 1}},
    )

    report = proposal_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["proposal_outcome"] == "NO_NEW_SEAM_MODEL_CLASS_JUSTIFIED_YET"
