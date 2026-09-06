from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_review_v0
    as review,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_exact_packet_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES
    assert report["authority"]["authorized_diagnosis_execution_count"] == 1
    assert report["authority"]["performed_diagnosis_execution_count"] == 0


def test_all_39_cases_reproduce_strict_nonoverlap() -> None:
    domain = _report()["independent_domain_reproduction"]
    assert domain["case_count"] == 39
    assert domain["all_D_gt_R1_plus_R2"] is True
    assert domain["all_reported_gaps_positive"] is True
    assert domain["all_reconstructed_gaps_positive"] is True
    assert domain["maximum_gap_reconstruction_absolute_error_m"] <= 2e-17
    assert domain["minimum_surface_gap_m"] == 1e-4
    assert len(domain["rows"]) == 39


def test_dimensionless_grid_covers_all_required_regimes_and_legacy_cases() -> None:
    domain = _report()["independent_domain_reproduction"]
    for key in (
        "wide_separation_present",
        "small_positive_gap_present",
        "lambda_much_less_than_gap_present",
        "lambda_comparable_to_gap_present",
        "lambda_comparable_to_radius_present",
        "lambda_much_greater_than_geometry_present",
    ):
        assert domain[key] is True, key
    assert domain["legacy_case_ids"] == [
        "LEGACY_STAGE_A_00", "LEGACY_STAGE_A_01", "LEGACY_STAGE_A_02"
    ]
    assert domain["ratio_ranges"]["g_over_lambda"]["maximum"] == 10.0
    assert math.isclose(
        domain["ratio_ranges"]["R2_over_lambda"]["maximum"],
        1000.0,
        rel_tol=1e-15,
        abs_tol=0.0,
    )


def test_newtonian_and_yukawa_derivations_units_and_normalization_pass() -> None:
    oracle = _report()["independent_oracle_contract_reproduction"]
    assert oracle["newtonian_derivation"]["passed"] is True
    assert oracle["newtonian_derivation"]["unit_reduction"].endswith("=J")
    yukawa = oracle["yukawa_derivation"]
    assert yukawa["passed"] is True
    assert yukawa["amplitude"] == 1.0 / 3.0
    assert yukawa["both_form_factors_present"] is True
    assert yukawa["center_distance_exponential_present"] is True
    assert yukawa["stable_gap_exponential_present"] is True
    assert yukawa["separate_from_newtonian_shell_statement"] is True


def test_stable_small_and_large_x_paths_cover_the_frozen_domain() -> None:
    row = _report()["independent_oracle_contract_reproduction"]["stable_evaluation"]
    assert row["x_min"] == 0.02
    assert math.isclose(row["x_max"], 1000.0, rel_tol=1e-15, abs_tol=0.0)
    assert "x^2/10" in row["small_x_series"]
    assert row["small_x_branch_max"] == 1e-3
    assert row["small_x_branch_active_on_frozen_grid"] is False
    assert row["large_x_scaled_branch_required"] is True
    assert "exp(-2*x)" in row["stable_scaled_factor"]
    assert "exp(-g/lambda)" in row["stable_combined_yukawa"]
    assert row["radial_cross_oracle_covers_all_frozen_cases"] is True
    assert row["passed"] is True


def test_all_four_paths_are_genuinely_distinguished() -> None:
    row = _report()["independent_oracle_contract_reproduction"]["path_independence"]
    assert len(row["path_ids"]) == len(set(row["path_ids"])) == 4
    assert row["analytic_production_import_forbidden"] is True
    assert row["nearby_order_is_not_oracle"] is True
    assert row["analytic_mathematical_path"] != row["production_coordinate_path"]
    assert row["reduced_mathematical_path"] != row["production_coordinate_path"]
    assert row["passed"] is True


def test_references_self_converge_before_production_and_fail_closed_on_budget() -> None:
    row = _report()["independent_oracle_contract_reproduction"]["self_convergence"]
    assert row["semi_analytic_precision_ladder"] == [50, 80, 120]
    assert row["direct_precision_ladder"] == [50, 80, 120]
    assert row["direct_adaptive_degree_ladder"] == [6, 8, 10]
    assert row["absolute_tolerance_J"] == 1e-36
    assert row["relative_tolerance"] == 1e-10
    assert row["plateau_before_production_judgment"] is True
    assert row["budget_exhaustion_behavior"] == "FAIL_CLOSED_REFERENCE_ORACLE_INADEQUATE"
    assert row["work_caps"] == {
        "evaluations_per_anchor": 2_000_000,
        "seconds_per_anchor": 180,
        "total_seconds": 3600,
        "memory_mib": 4096,
    }
    assert row["passed"] is True


def test_components_near_contact_and_torque_ordering_are_executable() -> None:
    decision = _report()["independent_decision_contract_reproduction"]
    assert decision["component_separation"]["passed"] is True
    assert decision["component_separation"]["combined_cannot_decide"] is True
    assert decision["near_contact"]["passed"] is True
    assert decision["near_contact"]["chi_edges"] == [0.0, 0.25, 1.0, 4.0, "INF"]
    assert decision["near_contact"]["improvement_factor"] == 10.0
    assert decision["torque_ordering"]["passed"] is True
    assert decision["torque_ordering"]["path_count"] == 3
    assert len(decision["torque_ordering"]["finite_difference_steps"]) == 4


def test_analytic_dft_and_alias_isolation_are_exact() -> None:
    row = _report()["independent_decision_contract_reproduction"]["dft_isolation"]
    assert row["passed"] is True
    assert row["sample_counts"] == [32, 64, 128, 256, 512, 1024]
    assert row["retained_harmonics"] == [2, 4, 6]
    assert row["expected_coefficient"] == "c_n=(A_n/2)*exp(i*phi_n)"
    assert row["alias_harmonic"] == 258
    assert row["classification_rule"] == {
        "analytic_fails": "ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE",
        "analytic_passes_production_fails": "KERNEL_NOISE_DRIVES_DFT_FAILURE",
    }


def test_ten_mutations_must_use_live_diagnostic_paths() -> None:
    row = _report()["independent_decision_contract_reproduction"]["mutation_routing"]
    assert row["mutation_count"] == row["row_count"] == 10
    assert row["distinct_designated_controls"] == 10
    assert row["live_production_path_required"] is True
    assert row["test_substitute_forbidden"] == "FORBIDDEN"
    assert row["passed"] is True


def test_root_cause_labels_are_multilabel_evidence_triggered_and_fail_unresolved() -> None:
    row = _report()["independent_decision_contract_reproduction"]["root_cause_labels"]
    assert row["multilabel"] is True
    assert row["principal_outcome_count"] == 7
    assert row["priority_is_permutation"] is True
    assert row["oracle_availability_count"] == 2
    for key in (
        "implementation_predicate",
        "fixed_order_predicate",
        "near_contact_predicate",
        "reference_predicate",
        "economic_predicate",
    ):
        assert row[key], key
    assert row["unresolved_behavior"].startswith("UNRESOLVED")
    assert row["passed"] is True


def test_all_36_independent_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 36
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_exactly_one_diagnosis_and_no_remedy() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "independent_packet_review_executed",
        "packet_custody_verified",
        "kernel_diagnosis_contract_ready",
        "one_bounded_diagnosis_execution_authorized",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key
    accepted = _report()["accepted_contract"]
    assert accepted["diagnosis_execution_authorized"] == 1
    assert accepted["diagnosis_execution_performed"] == 0
    assert accepted["required_stop"] == "INDEPENDENT_DIAGNOSIS_RESULT_REVIEW"


def test_human_review_records_nonoverlap_oracles_stability_and_stop() -> None:
    text = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "36 / 36 GATES PASSED",
        "39 / 39",
        "x=R/lambda=1000",
        "1e-36 J + 1e-10",
        "n=258",
        review.SELECTED_NEXT_TARGET,
        "does not authorize implementation correction",
    ):
        assert token in text
