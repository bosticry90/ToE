from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_v0
    as packet,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_and_consumes_exact_selector_authority() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["status"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_selector_artifacts"]
    } == packet.SELECTOR_HASHES


def test_exact_39_case_nonoverlap_grid_is_frozen() -> None:
    domain = _report()["diagnostic_domain"]
    assert domain["stratified_case_count"] == 36
    assert domain["legacy_case_count"] == 3
    assert domain["total_case_count"] == 39
    assert len(domain["radius_pairs_m"]) == 3
    assert domain["surface_gaps_m"] == [1e-4, 1e-3, 1e-2]
    assert len(domain["rows"]) == 39
    assert all(row["strictly_nonoverlapping"] for row in domain["rows"])
    assert all(row["center_distance_m"] > row["radius_1_m"] + row["radius_2_m"] for row in domain["rows"])
    assert domain["high_precision_anchor_count"] == 12
    assert domain["post_result_case_selection"] == "FORBIDDEN"


def test_lambda_strata_and_legacy_failure_cases_are_exact() -> None:
    domain = _report()["diagnostic_domain"]
    assert domain["lambda_formulas"] == {
        "SHORT_VS_GAP": "g/10",
        "GAP_TRANSITION": "g",
        "RADIUS_TRANSITION": "sqrt(R1*R2)",
        "LONG_VS_GEOMETRY": "10*max(g,sqrt(R1*R2))",
    }
    assert domain["legacy_cases"] == [
        {"case_id": "LEGACY_STAGE_A_00", "center_distance_m": 0.011, "lambda_m": 1e-4},
        {"case_id": "LEGACY_STAGE_A_01", "center_distance_m": 0.03, "lambda_m": 5e-3},
        {"case_id": "LEGACY_STAGE_A_02", "center_distance_m": 0.08, "lambda_m": 0.1},
    ]


def test_components_are_separate_and_combined_cannot_mask_accuracy() -> None:
    row = _report()["component_contract"]
    assert row["components"] == ["NEWTONIAN", "YUKAWA", "COMBINED_DIAGNOSTIC_ONLY"]
    assert len(row["per_component_records"]) == 6
    assert row["combined_records"] == ["VALUE_J", "CANCELLATION_RATIO"]
    assert row["combined_value_may_decide_component_accuracy"] is False
    assert "abs(U_N)+abs(U_Y)" in row["cancellation_ratio"]


def test_exact_newtonian_and_yukawa_oracles_are_frozen_independently() -> None:
    oracle = _report()["analytic_oracle_contract"]
    assert oracle["domain"] == "STRICTLY_NONOVERLAPPING_HOMOGENEOUS_SPHERES_ONLY"
    assert oracle["newtonian"] == "U_N(D)=-G*M1*M2/D"
    assert oracle["sphere_form_factor"] == "F(x)=3*(x*cosh(x)-sinh(x))/x^3"
    assert "exp(-D/lambda)" in oracle["yukawa"]
    assert "exp(-g/lambda)" in oracle["stable_yukawa"]
    assert oracle["small_x_branch_max"] == 1e-3
    assert oracle["independent_implementation_required"] is True
    assert oracle["production_form_factor_function_import_forbidden"] is True
    assert len(oracle["derivation_obligations"]) == 5


def test_four_genuinely_distinct_paths_and_ladders_are_frozen() -> None:
    paths = _report()["evaluation_paths"]
    assert paths["path_count"] == 4
    assert paths["production_fixed_tensor"]["orders"] == [8, 12, 16, 24, 32, 48]
    assert paths["production_fixed_tensor"]["dimensions_refined_together"] == [
        "r1", "mu1", "r2", "mu2"
    ]
    assert paths["analytic_closed_form"]["precision_decimal_digits"] == 120
    assert paths["semi_analytic_radial"]["precision_decimal_digits"] == [50, 80, 120]
    assert paths["adaptive_direct_density"]["tanh_sinh_max_degrees"] == [6, 8, 10]
    assert paths["adaptive_direct_density"]["anchor_case_count"] == 12
    assert paths["nearby_order_same_path_is_independent_oracle"] is False


def test_oracle_self_convergence_and_work_limits_are_quantitative() -> None:
    row = _report()["oracle_convergence_and_work_contract"]
    assert row["absolute_energy_tolerance_J"] == 1e-36
    assert row["relative_energy_tolerance"] == 1e-10
    assert row["reference_must_plateau_before_judging_production"] is True
    assert row["higher_cost_alone_implies_correctness"] is False
    assert row["maximum_function_evaluations_per_direct_anchor"] == 2_000_000
    assert row["maximum_wall_clock_seconds_per_direct_anchor"] == 180
    assert row["maximum_total_wall_clock_seconds"] == 3600
    assert row["maximum_memory_mib"] == 4096
    assert row["result_dependent_tolerance_or_budget_change"] == "FORBIDDEN"


def test_near_contact_precision_summation_and_symmetry_are_frozen() -> None:
    report = _report()
    near = report["near_contact_contract"]
    assert near["chi_bin_edges"] == [0.0, 0.25, 1.0, 4.0, "INF"]
    assert near["dominant_near_contact_rule"].endswith(">=0.90")
    assert near["domain_decomposition_probe"]["required_improvement_factor"] == 10.0
    precision = report["precision_summation_and_symmetry_contract"]
    assert len(precision["precision_levels"]) == 4
    assert len(precision["summation_methods"]) == 4
    assert precision["explicit_azimuth_control"]["azimuth_sample_counts"] == [32, 64]


def test_energy_must_pass_before_torque_and_no_final_vector_is_allowed() -> None:
    row = _report()["torque_isolation_contract"]
    assert row["execution_order"] == "PAIR_ENERGY_ORACLES_MUST_PASS_BEFORE_TORQUE_TESTS"
    assert row["gaps_m"] == [1e-4, 1e-3, 1e-2]
    assert row["lambda_m"] == [1e-4, 1e-3, 1e-2]
    assert len(row["angles_rad"]) == 2
    assert row["component_modes"] == ["NEWTONIAN", "YUKAWA"]
    assert len(row["torque_paths"]) == 3
    assert row["finite_difference_steps_rad"] == [1e-3, 5e-4, 2.5e-4, 1.25e-4]
    assert row["final_apparatus_harmonic_vector_prohibited"] is True


def test_analytic_dft_and_alias_probe_are_exact() -> None:
    row = _report()["angular_dft_contract"]
    assert row["sample_counts"] == [32, 64, 128, 256, 512, 1024]
    assert row["retained_harmonics"] == [2, 4, 6]
    assert [item["n"] for item in row["analytic_signal"]["rows"]] == [2, 4, 6]
    assert row["analytic_signal"]["expected_coefficient"] == "c_n=(A_n/2)*exp(i*phi_n)"
    assert row["analytic_signal"]["absolute_tolerance_N_m"] == 1e-28
    assert row["analytic_signal"]["relative_tolerance"] == 1e-12
    assert row["alias_probe"]["harmonic"] == 258
    assert row["production_torque_test_gate"] == "PAIR_ENERGY_AND_TORQUE_ORACLES_PASS_FIRST"


def test_all_ten_mutations_route_through_the_diagnostic_path() -> None:
    mutations = _report()["mutation_controls"]
    assert mutations["mutation_count"] == 10
    assert len(mutations["rows"]) == 10
    assert mutations["production_diagnostic_path_required"] is True
    assert mutations["test_only_substitute_path"] == "FORBIDDEN"
    assert {row["mutation_id"] for row in mutations["rows"]} == {
        "REMOVE_ONE_RADIAL_VOLUME_FACTOR_R_SQUARED",
        "INTERPRET_RADIUS_AS_DIAMETER",
        "USE_SURFACE_GAP_AS_CENTER_DISTANCE",
        "REPLACE_A_Y_ONE_THIRD_BY_ONE",
        "FLIP_YUKAWA_EXPONENTIAL_SIGN",
        "FLIP_NEGATIVE_ANGULAR_ENERGY_DERIVATIVE_SIGN",
        "LEAVE_MU2_AT_ORDER_8_WHILE_OTHER_DIMENSIONS_REFINE",
        "REMOVE_ONE_SPHERE_FORM_FACTOR",
        "DOUBLE_DFT_NORMALIZATION",
        "REVERSE_DFT_PHASE_SIGN",
    }


def test_root_cause_and_oracle_availability_vocabularies_are_separate() -> None:
    row = _report()["root_cause_adjudication"]
    assert row["multilabel_reporting"] is True
    assert row["principal_outcomes"] == list(packet.PRINCIPAL_ROOT_CAUSE_OUTCOMES)
    assert row["oracle_availability_outcomes"] == list(packet.ORACLE_AVAILABILITY_OUTCOMES)
    assert row["principal_priority"][0] == "REFERENCE_ORACLE_INADEQUATE"
    assert row["no_root_cause_rounding"].startswith("UNRESOLVED")


def test_outputs_and_review_authority_remain_bounded() -> None:
    report = _report()
    assert len(report["authorized_diagnostic_outputs"]) == 10
    assert report["forbidden_outputs"] == [
        "FINAL_REAL_150_APPARATUS_VECTOR",
        "SEVENTEEN_COLUMN_JACOBIAN",
        "SINGULAR_VALUES",
        "ETA_LAMBDA",
        "IDENTIFIABILITY_RESULT",
        "SYNTHETIC_NOISE",
        "SENSITIVITY_FORECAST",
        "SCALAR_RANGE_OR_ALPHA_CONCLUSION",
    ]
    review = report["packet_review_contract"]
    assert review["review_outcomes"] == list(packet.PACKET_REVIEW_OUTCOMES)
    assert review["ready_outcome_authorizes"] == "ONE_BOUNDED_DIAGNOSIS_EXECUTION_ONLY"
    assert len(review["ready_outcome_does_not_authorize"]) == 6
    assert review["post_diagnosis_independent_result_review_required"] is True


def test_all_thirty_preparation_gates_pass_without_execution() -> None:
    gates = _report()["preparation_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 30
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])
    assert _report()["work_packages"]["count"] == 9
    assert _report()["work_packages"]["executed_count"] == 0


def test_scope_records_preparation_only_and_all_scientific_work_unexecuted() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "diagnosis_packet_prepared",
        "selector_authority_consumed",
        "diagnostic_case_grid_constructed_as_contract_metadata",
        "diagnosis_packet_independent_review_required",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_packet_records_grid_oracles_mutations_and_stop() -> None:
    text = (ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "39 total rows",
        "All 12 frozen",
        "1e-36 J + 1e-10",
        "n=258",
        "Ten production-routed mutations",
        "nine unexecuted work packages",
        packet.SELECTED_NEXT_TARGET,
        "NOT AUTHORIZED",
    ):
        assert token in text
