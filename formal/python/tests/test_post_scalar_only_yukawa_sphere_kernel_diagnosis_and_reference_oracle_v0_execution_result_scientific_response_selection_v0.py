from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    post_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0_execution_result_scientific_response_selection_v0
    as selection,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selection.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selector_regenerates_and_freezes_review_authority() -> None:
    assert selection.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_result_review_artifacts"]
    } == selection.AUTHORITY_HASHES


def test_analytic_oracle_route_is_unique_baseline_winner() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 220
    assert ranking["runner_up_candidate_id"] == "FAILED_EXECUTION_PERFORMANCE_DIAGNOSIS"
    assert ranking["runner_up_score"] == 153
    assert ranking["winning_margin"] == 67
    assert len(ranking["rows"]) == 5


def test_direct_method_replacement_is_explicitly_ranked_below_oracle() -> None:
    rows = _report()["ranking"]["rows"]
    identifiers = [row["candidate_id"] for row in rows]
    assert "DIRECT_INTEGRATION_METHOD_REPLACEMENT" in identifiers
    assert identifiers.index(selection.SELECTED_CANDIDATE_ID) < identifiers.index(
        "DIRECT_INTEGRATION_METHOD_REPLACEMENT"
    )


def test_selection_is_stable_in_all_30_sensitivity_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 30
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] == 47
    assert all(
        row["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
        for row in sensitivity["rows"]
    )


def test_packet_scope_is_small_and_excludes_the_failed_diagnosis() -> None:
    requirements = _report()["analytic_oracle_packet_preparation_requirements"]
    assert requirements["case_grid"]["minimum_case_count"] == 6
    assert requirements["case_grid"]["maximum_case_count"] == 9
    assert requirements["independent_cross_check"]["path_count"] == 1
    assert requirements["independent_cross_check"]["all_39_cases_forbidden"] is True
    assert requirements["independent_cross_check"]["production_cubature_import_forbidden"] is True


def test_formula_and_stable_evaluator_burdens_are_explicit() -> None:
    requirements = _report()["analytic_oracle_packet_preparation_requirements"]
    formula = requirements["formula_contract"]
    evaluator = requirements["stable_evaluator"]
    assert formula["yukawa_amplitude"] == "A_Y=1/3"
    assert formula["independent_derivation_required"] is True
    assert evaluator["small_x_series_required"] is True
    assert evaluator["moderate_x_direct_regime_required"] is True
    assert evaluator["large_x_scaled_or_log_regime_required"] is True
    assert evaluator["overlap_continuity_tests_required"] is True


def test_future_timeout_and_process_custody_is_mandatory() -> None:
    custody = _report()["analytic_oracle_packet_preparation_requirements"]["execution_custody"]
    assert custody == {
        "child_termination_timestamps_preserved": True,
        "completed_stage_values_decision_bearing_only_if_preregistered": True,
        "orphan_child_survival_is_execution_failure": True,
        "process_group_termination_mandatory": True,
        "raw_launcher_log_preserved": True,
        "stage_level_atomic_status_preserved": True,
        "timeout_initiation_timestamp_preserved": True,
    }


def test_only_success_can_enable_later_production_comparison() -> None:
    requirements = _report()["analytic_oracle_packet_preparation_requirements"]
    assert requirements["legitimate_outcomes"] == [
        "ANALYTIC_SPHERE_ORACLE_QUALIFIED",
        "ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE",
        "ANALYTIC_ORACLE_CROSS_CHECK_FAILED",
        "ANALYTIC_ORACLE_QUALIFICATION_TIMEOUT",
        "SPHERE_ORACLE_NOT_VALID_OVER_REQUIRED_DOMAIN",
    ]
    assert requirements["only_success_eligibility"].startswith(
        "Only ANALYTIC_SPHERE_ORACLE_QUALIFIED"
    )


def test_selector_does_not_prepare_or_execute_the_packet() -> None:
    scope = _report()["scope"]
    assert scope["analytic_oracle_packet_preparation_authorized"] is True
    assert scope["analytic_oracle_packet_prepared_now"] is False
    assert scope["analytic_oracle_qualification_executed"] is False
    assert scope["production_method_replacement_authorized"] is False
    assert scope["diagnosis_rerun_authorized"] is False
    assert scope["stage_b_authorized"] is False


def test_next_target_and_human_record_are_exact() -> None:
    report = _report()
    assert report["selected_route"] == selection.SELECTED_ROUTE
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    human = (ROOT / selection.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    assert selection.SELECTED_ROUTE in human
    assert selection.SELECTED_NEXT_TARGET in human
    assert "process-group termination" in human

