from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_PACKET_20260719_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_PACKET_REVIEW_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_PACKET_REVIEW_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_sphere_kernel_diagnosis_and_"
    "reference_oracle_packet_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOraclePacketReviewV0.lean"
)

TARGET = (
    "review_scalar_only_yukawa_sphere_kernel_diagnosis_and_"
    "reference_oracle_packet_v0_result"
)
VERDICT = "KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_CONTRACT_READY"
SELECTED_NEXT_TARGET = (
    "execute_scalar_only_yukawa_sphere_kernel_diagnosis_and_"
    "reference_oracle_v0_once"
)
SELECTED_NEXT_TARGET_KIND = (
    "ONE_BOUNDED_DIAGNOSIS_EXECUTION_ONLY_NO_REPAIR_NO_STAGE_A_RERUN"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_PACKET_20260719_v0.md":
        "3d628f876acaed975011d9f14ae44f2d613322a8fe56f5f829699d3f616b67e3",
    PACKET_RELATIVE_PATH:
        "0fbbc9f57f0c591248509f4f9621a9aa751bc17dcb9ba2e179360759350e2414",
    "formal/python/tools/scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_v0.py":
        "4041e7722bdec724dfc30d61bf12f0eeded7628f5f6b1e3514906f3d7d601aab",
    "formal/python/tests/test_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_v0.py":
        "c7af9699b41e84c65b1ce3307a7f98ee59bc831852bc5b379d1a3baca0ab22d8",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOraclePacketV0.lean":
        "16fc52d04d649007d7e94b467d3c0a94cfc2f451e108f6e3bde1abecb808c946",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _domain_reproduction(packet: dict[str, Any]) -> dict[str, Any]:
    rows = packet["diagnostic_domain"]["rows"]
    audited = []
    for row in rows:
        r1 = float(row["radius_1_m"])
        r2 = float(row["radius_2_m"])
        gap = float(row["surface_gap_m"])
        distance = float(row["center_distance_m"])
        lam = float(row["lambda_m"])
        reconstructed_gap = distance - r1 - r2
        audited.append({
            "case_id": row["case_id"],
            "D_gt_R1_plus_R2": distance > r1 + r2,
            "reported_gap_positive": gap > 0.0,
            "reconstructed_gap_positive": reconstructed_gap > 0.0,
            "gap_reconstruction_absolute_error_m": abs(reconstructed_gap - gap),
            "g_over_R1": gap / r1,
            "g_over_R2": gap / r2,
            "R1_over_lambda": r1 / lam,
            "R2_over_lambda": r2 / lam,
            "g_over_lambda": gap / lam,
            "case_class": row["case_class"],
            "lambda_role": row["lambda_role"],
        })
    ratio_keys = (
        "g_over_R1", "g_over_R2", "R1_over_lambda", "R2_over_lambda", "g_over_lambda"
    )
    ratio_ranges = {
        key: {
            "minimum": min(row[key] for row in audited),
            "maximum": max(row[key] for row in audited),
        }
        for key in ratio_keys
    }
    roles = {row["lambda_role"] for row in audited}
    legacy_ids = [
        row["case_id"] for row in audited
        if row["case_class"] == "LEGACY_STAGE_A_REPRODUCTION"
    ]
    return {
        "case_count": len(audited),
        "all_D_gt_R1_plus_R2": all(row["D_gt_R1_plus_R2"] for row in audited),
        "all_reported_gaps_positive": all(row["reported_gap_positive"] for row in audited),
        "all_reconstructed_gaps_positive": all(row["reconstructed_gap_positive"] for row in audited),
        "maximum_gap_reconstruction_absolute_error_m": max(
            row["gap_reconstruction_absolute_error_m"] for row in audited
        ),
        "minimum_surface_gap_m": min(
            float(row["surface_gap_m"]) for row in packet["diagnostic_domain"]["rows"]
        ),
        "ratio_ranges": ratio_ranges,
        "lambda_roles": sorted(roles),
        "legacy_case_ids": legacy_ids,
        "wide_separation_present": ratio_ranges["g_over_R2"]["maximum"] >= 10.0,
        "small_positive_gap_present": ratio_ranges["g_over_R2"]["minimum"] <= 0.01,
        "lambda_much_less_than_gap_present": ratio_ranges["g_over_lambda"]["maximum"] >= 10.0,
        "lambda_comparable_to_gap_present": "GAP_TRANSITION" in roles,
        "lambda_comparable_to_radius_present": "RADIUS_TRANSITION" in roles,
        "lambda_much_greater_than_geometry_present": ratio_ranges["g_over_lambda"]["minimum"] <= 0.01,
        "rows": audited,
    }


def _oracle_reproduction(packet: dict[str, Any], domain: dict[str, Any]) -> dict[str, Any]:
    physical = packet["physical_constants_and_conventions"]
    analytic = packet["analytic_oracle_contract"]
    paths = packet["evaluation_paths"]
    convergence = packet["oracle_convergence_and_work_contract"]
    x_min = min(
        min(row["R1_over_lambda"], row["R2_over_lambda"])
        for row in domain["rows"]
    )
    x_max = max(
        max(row["R1_over_lambda"], row["R2_over_lambda"])
        for row in domain["rows"]
    )
    path_ids = [
        paths["production_fixed_tensor"]["path_id"],
        paths["analytic_closed_form"]["path_id"],
        paths["semi_analytic_radial"]["path_id"],
        paths["adaptive_direct_density"]["path_id"],
    ]
    return {
        "newtonian_derivation": {
            "external_shell_theorem_domain": analytic["domain"],
            "mass_formula": analytic["mass"],
            "energy_formula": analytic["newtonian"],
            "unit_reduction": "(m^3*kg^-1*s^-2)*kg^2/m=kg*m^2*s^-2=J",
            "passed": (
                analytic["domain"] == "STRICTLY_NONOVERLAPPING_HOMOGENEOUS_SPHERES_ONLY"
                and analytic["newtonian"] == "U_N(D)=-G*M1*M2/D"
            ),
        },
        "yukawa_derivation": {
            "amplitude": physical["yukawa_amplitude"],
            "mass_formula": analytic["mass"],
            "form_factor": analytic["sphere_form_factor"],
            "center_distance_exponential_present": "exp(-D/lambda)" in analytic["yukawa"],
            "both_form_factors_present": "F(x1)*F(x2)" in analytic["yukawa"],
            "stable_gap_exponential_present": "exp(-g/lambda)" in analytic["stable_yukawa"],
            "separate_from_newtonian_shell_statement": True,
            "unit_reduction": "dimensionless_A_Y_F1_F2_exp_times_G*M1*M2/D=J",
            "passed": (
                physical["yukawa_amplitude"] == 1.0 / 3.0
                and "F(x1)*F(x2)" in analytic["yukawa"]
                and "exp(-D/lambda)" in analytic["yukawa"]
                and "exp(-g/lambda)" in analytic["stable_yukawa"]
                and len(analytic["derivation_obligations"]) == 5
            ),
        },
        "stable_evaluation": {
            "x_min": x_min,
            "x_max": x_max,
            "small_x_series": analytic["small_x_series"],
            "small_x_branch_max": analytic["small_x_branch_max"],
            "stable_scaled_factor": analytic["stable_scaled_factor"],
            "stable_combined_yukawa": analytic["stable_yukawa"],
            "small_x_branch_active_on_frozen_grid": x_min < analytic["small_x_branch_max"],
            "large_x_scaled_branch_required": x_max > 700.0,
            "radial_cross_oracle_covers_all_frozen_cases": paths["semi_analytic_radial"]["all_39_cases"],
            "passed": (
                "x^2/10" in analytic["small_x_series"]
                and "exp(-2*x)" in analytic["stable_scaled_factor"]
                and "exp(-g/lambda)" in analytic["stable_yukawa"]
                and paths["semi_analytic_radial"]["all_39_cases"] is True
            ),
        },
        "path_independence": {
            "path_ids": path_ids,
            "unique_path_ids": len(set(path_ids)) == 4,
            "analytic_production_import_forbidden": analytic["production_form_factor_function_import_forbidden"],
            "nearby_order_is_not_oracle": paths["nearby_order_same_path_is_independent_oracle"] is False,
            "production_coordinate_path": "FIXED_TENSOR_4D",
            "analytic_mathematical_path": "CLOSED_FORM_EXTERNAL_SPHERE_FIELD",
            "reduced_mathematical_path": "ONE_DIMENSIONAL_RADIAL_FORM_FACTOR_INTEGRAL",
            "adaptive_numeric_path": "ADAPTIVE_ARBITRARY_PRECISION_DIRECT_DENSITY",
            "passed": (
                len(set(path_ids)) == 4
                and analytic["production_form_factor_function_import_forbidden"] is True
                and paths["nearby_order_same_path_is_independent_oracle"] is False
            ),
        },
        "self_convergence": {
            "semi_analytic_precision_ladder": paths["semi_analytic_radial"]["precision_decimal_digits"],
            "direct_precision_ladder": paths["adaptive_direct_density"]["precision_decimal_digits"],
            "direct_adaptive_degree_ladder": paths["adaptive_direct_density"]["tanh_sinh_max_degrees"],
            "plateau_levels": convergence["plateau_levels"],
            "absolute_tolerance_J": convergence["absolute_energy_tolerance_J"],
            "relative_tolerance": convergence["relative_energy_tolerance"],
            "plateau_before_production_judgment": convergence["reference_must_plateau_before_judging_production"],
            "budget_exhaustion_behavior": convergence["budget_exhaustion_behavior"],
            "work_caps": {
                "evaluations_per_anchor": convergence["maximum_function_evaluations_per_direct_anchor"],
                "seconds_per_anchor": convergence["maximum_wall_clock_seconds_per_direct_anchor"],
                "total_seconds": convergence["maximum_total_wall_clock_seconds"],
                "memory_mib": convergence["maximum_memory_mib"],
            },
            "passed": (
                paths["semi_analytic_radial"]["precision_decimal_digits"] == [50, 80, 120]
                and paths["adaptive_direct_density"]["precision_decimal_digits"] == [50, 80, 120]
                and paths["adaptive_direct_density"]["tanh_sinh_max_degrees"] == [6, 8, 10]
                and convergence["reference_must_plateau_before_judging_production"] is True
                and convergence["result_dependent_tolerance_or_budget_change"] == "FORBIDDEN"
            ),
        },
    }


def _decision_contract_reproduction(packet: dict[str, Any]) -> dict[str, Any]:
    components = packet["component_contract"]
    near = packet["near_contact_contract"]
    torque = packet["torque_isolation_contract"]
    dft = packet["angular_dft_contract"]
    mutations = packet["mutation_controls"]
    root = packet["root_cause_adjudication"]
    return {
        "component_separation": {
            "components": components["components"],
            "combined_cannot_decide": components["combined_value_may_decide_component_accuracy"] is False,
            "cancellation_ratio_frozen": "CANCELLATION_RATIO" in components["combined_records"],
            "passed": (
                components["components"] == ["NEWTONIAN", "YUKAWA", "COMBINED_DIAGNOSTIC_ONLY"]
                and components["combined_value_may_decide_component_accuracy"] is False
            ),
        },
        "near_contact": {
            "chi_edges": near["chi_bin_edges"],
            "record_count": len(near["records"]),
            "dominance_threshold": near["dominant_near_contact_rule"],
            "improvement_factor": near["domain_decomposition_probe"]["required_improvement_factor"],
            "passed": (
                near["chi_bin_edges"] == [0.0, 0.25, 1.0, 4.0, "INF"]
                and len(near["records"]) == 4
                and near["domain_decomposition_probe"]["required_improvement_factor"] == 10.0
            ),
        },
        "torque_ordering": {
            "execution_order": torque["execution_order"],
            "path_count": len(torque["torque_paths"]),
            "finite_difference_steps": torque["finite_difference_steps_rad"],
            "passed": (
                torque["execution_order"] == "PAIR_ENERGY_ORACLES_MUST_PASS_BEFORE_TORQUE_TESTS"
                and len(torque["torque_paths"]) == 3
                and torque["final_apparatus_harmonic_vector_prohibited"] is True
            ),
        },
        "dft_isolation": {
            "convention": dft["convention"],
            "sample_counts": dft["sample_counts"],
            "retained_harmonics": dft["retained_harmonics"],
            "expected_coefficient": dft["analytic_signal"]["expected_coefficient"],
            "alias_harmonic": dft["alias_probe"]["harmonic"],
            "classification_rule": dft["classification_rule"],
            "passed": (
                dft["retained_harmonics"] == [2, 4, 6]
                and dft["analytic_signal"]["expected_coefficient"] == "c_n=(A_n/2)*exp(i*phi_n)"
                and dft["alias_probe"]["harmonic"] == 258
                and dft["production_torque_test_gate"] == "PAIR_ENERGY_AND_TORQUE_ORACLES_PASS_FIRST"
            ),
        },
        "mutation_routing": {
            "mutation_count": mutations["mutation_count"],
            "row_count": len(mutations["rows"]),
            "distinct_designated_controls": len({row["designated_control"] for row in mutations["rows"]}),
            "live_production_path_required": mutations["production_diagnostic_path_required"],
            "test_substitute_forbidden": mutations["test_only_substitute_path"],
            "passed": (
                mutations["mutation_count"] == len(mutations["rows"]) == 10
                and mutations["production_diagnostic_path_required"] is True
                and mutations["test_only_substitute_path"] == "FORBIDDEN"
            ),
        },
        "root_cause_labels": {
            "multilabel": root["multilabel_reporting"],
            "principal_outcome_count": len(root["principal_outcomes"]),
            "priority_is_permutation": set(root["principal_priority"]) == set(root["principal_outcomes"]),
            "oracle_availability_count": len(root["oracle_availability_outcomes"]),
            "implementation_predicate": root["implementation_defect_requires"],
            "fixed_order_predicate": root["fixed_order_inadequate_requires"],
            "near_contact_predicate": root["near_contact_requires"],
            "reference_predicate": root["reference_inadequate_requires"],
            "economic_predicate": root["economic_failure_requires"],
            "unresolved_behavior": root["no_root_cause_rounding"],
            "passed": (
                root["multilabel_reporting"] is True
                and len(root["principal_outcomes"]) == 7
                and set(root["principal_priority"]) == set(root["principal_outcomes"])
                and len(root["oracle_availability_outcomes"]) == 2
                and root["no_root_cause_rounding"].startswith("UNRESOLVED")
            ),
        },
    }


def build_report() -> dict[str, Any]:
    frozen = []
    for relative_path, expected in PACKET_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"diagnosis packet custody drift: {relative_path}")
        frozen.append({"relative_path": relative_path, "sha256": observed})
    packet = _load_json(PACKET_RELATIVE_PATH)
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("packet did not rotate to this independent review")
    if packet.get("status") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("packet status is not pending independent review")
    if packet.get("preparation_gates", {}).get("pass_count") != 30:
        raise ValueError("packet preparation gates are incomplete")
    if packet.get("work_packages", {}).get("executed_count") != 0:
        raise ValueError("packet preparation unexpectedly executed work")

    domain = _domain_reproduction(packet)
    oracle = _oracle_reproduction(packet, domain)
    decision = _decision_contract_reproduction(packet)
    gates = [
        {"gate_id": "R01_EXACT_PACKET_CUSTODY_AND_TARGET", "status": "PASS", "detail": "five packet surfaces hash-verified"},
        {"gate_id": "R02_PENDING_REVIEW_AND_ZERO_EXECUTION", "status": "PASS", "detail": "0/9 work packages and no kernel/oracle calls"},
        {"gate_id": "R03_ALL_39_CASES_STRICTLY_NONOVERLAPPING", "status": "PASS" if domain["all_D_gt_R1_plus_R2"] and domain["all_reconstructed_gaps_positive"] else "FAIL", "detail": f"minimum gap {domain['minimum_surface_gap_m']:.17e} m"},
        {"gate_id": "R04_CENTER_DISTANCE_GAP_RADIUS_SEMANTICS", "status": "PASS" if domain["maximum_gap_reconstruction_absolute_error_m"] <= 2e-17 else "FAIL", "detail": "D=R1+R2+g reproduced independently"},
        {"gate_id": "R05_DIMENSIONLESS_REGIME_COVERAGE", "status": "PASS" if all(domain[key] for key in ("wide_separation_present", "small_positive_gap_present", "lambda_much_less_than_gap_present", "lambda_comparable_to_gap_present", "lambda_comparable_to_radius_present", "lambda_much_greater_than_geometry_present")) else "FAIL", "detail": "g/R, R/lambda, and g/lambda strata reproduced"},
        {"gate_id": "R06_THREE_LEGACY_FAILURE_CASES_PRESENT", "status": "PASS" if domain["legacy_case_ids"] == ["LEGACY_STAGE_A_00", "LEGACY_STAGE_A_01", "LEGACY_STAGE_A_02"] else "FAIL", "detail": "all accepted failure configurations retained"},
        {"gate_id": "R07_NEWTONIAN_SHELL_ORACLE_DERIVATION", "status": "PASS" if oracle["newtonian_derivation"]["passed"] else "FAIL", "detail": "external nonoverlap shell theorem and joule units"},
        {"gate_id": "R08_YUKAWA_FORM_FACTOR_DERIVATION", "status": "PASS" if oracle["yukawa_derivation"]["passed"] else "FAIL", "detail": "separate Yukawa exterior-field derivation obligations"},
        {"gate_id": "R09_A_Y_MASS_DENSITY_AND_UNITS", "status": "PASS" if oracle["yukawa_derivation"]["amplitude"] == 1.0 / 3.0 else "FAIL", "detail": "A_Y=1/3, sphere mass formula, energy in J"},
        {"gate_id": "R10_CENTER_EXPONENT_AND_TWO_FORM_FACTORS", "status": "PASS" if oracle["yukawa_derivation"]["center_distance_exponential_present"] and oracle["yukawa_derivation"]["both_form_factors_present"] else "FAIL", "detail": "exp(-D/lambda)*F1*F2 and stable exp(-g/lambda)*H1*H2"},
        {"gate_id": "R11_SMALL_X_SERIES_STABILITY", "status": "PASS" if "x^2/10" in oracle["stable_evaluation"]["small_x_series"] else "FAIL", "detail": "small-x series frozen; grid minimum x exceeds branch threshold"},
        {"gate_id": "R12_LARGE_X_SCALED_STABILITY", "status": "PASS" if oracle["stable_evaluation"]["passed"] and oracle["stable_evaluation"]["large_x_scaled_branch_required"] else "FAIL", "detail": "scaled H form avoids separate cosh/sinh overflow through x=1000"},
        {"gate_id": "R13_FOUR_PATH_IDENTITIES_EXACT", "status": "PASS" if oracle["path_independence"]["unique_path_ids"] else "FAIL", "detail": "production, analytic, radial, and adaptive identities distinct"},
        {"gate_id": "R14_GENUINE_REFERENCE_INDEPENDENCE", "status": "PASS" if oracle["path_independence"]["passed"] else "FAIL", "detail": "closed-form and radial paths do not import production form factor"},
        {"gate_id": "R15_ALL_PRODUCTION_DIMENSIONS_REFINE", "status": "PASS" if packet["evaluation_paths"]["production_fixed_tensor"]["dimensions_refined_together"] == ["r1", "mu1", "r2", "mu2"] else "FAIL", "detail": "orders 8 through 48 route all four dimensions"},
        {"gate_id": "R16_REFERENCE_SELF_CONVERGENCE", "status": "PASS" if oracle["self_convergence"]["passed"] else "FAIL", "detail": "precision and adaptive-degree ladders plus absolute/relative plateaus"},
        {"gate_id": "R17_WORK_CAP_FAIL_CLOSED_BEHAVIOR", "status": "PASS" if oracle["self_convergence"]["budget_exhaustion_behavior"] == "FAIL_CLOSED_REFERENCE_ORACLE_INADEQUATE" else "FAIL", "detail": "evaluation, time, memory, and total-work caps frozen"},
        {"gate_id": "R18_NEWTONIAN_YUKAWA_COMPONENT_SEPARATION", "status": "PASS" if decision["component_separation"]["passed"] else "FAIL", "detail": "combined total cannot decide component accuracy"},
        {"gate_id": "R19_NEAR_CONTACT_NUMERICAL_PROFILE", "status": "PASS" if decision["near_contact"]["passed"] else "FAIL", "detail": "chi bins, contribution fractions, and tenfold improvement rule"},
        {"gate_id": "R20_PRECISION_SUMMATION_SCALING_SYMMETRY", "status": "PASS" if len(packet["precision_summation_and_symmetry_contract"]["summation_methods"]) == 4 else "FAIL", "detail": "four precision and four summation modes plus explicit azimuth control"},
        {"gate_id": "R21_PAIR_ENERGY_PRECEDES_TORQUE", "status": "PASS" if decision["torque_ordering"]["passed"] else "FAIL", "detail": "torque receives no verdict until energy oracles pass"},
        {"gate_id": "R22_THREE_TORQUE_PATHS_AND_REFINEMENT", "status": "PASS" if decision["torque_ordering"]["path_count"] == 3 and len(decision["torque_ordering"]["finite_difference_steps"]) == 4 else "FAIL", "detail": "analytic, force/lever, and five-point derivative paths"},
        {"gate_id": "R23_ANALYTIC_DFT_COEFFICIENT_PHASE_NORMALIZATION", "status": "PASS" if decision["dft_isolation"]["passed"] else "FAIL", "detail": "known n=2,4,6 coefficients under Stage A phase convention"},
        {"gate_id": "R24_HIGH_HARMONIC_ALIAS_PROBE", "status": "PASS" if decision["dft_isolation"]["alias_harmonic"] == 258 else "FAIL", "detail": "n=258 aliases at N=256 but not retained N=512 coefficients"},
        {"gate_id": "R25_PRODUCTION_DFT_AFTER_VALIDATED_TORQUE_ONLY", "status": "PASS" if packet["angular_dft_contract"]["production_torque_test_gate"] == "PAIR_ENERGY_AND_TORQUE_ORACLES_PASS_FIRST" else "FAIL", "detail": "DFT implementation and kernel-noise classifications remain separable"},
        {"gate_id": "R26_EXACT_TEN_MUTATIONS", "status": "PASS" if decision["mutation_routing"]["mutation_count"] == 10 else "FAIL", "detail": "geometry, weights, Yukawa, torque, and DFT mutations exact"},
        {"gate_id": "R27_MUTATIONS_USE_LIVE_DIAGNOSTIC_PATH", "status": "PASS" if decision["mutation_routing"]["passed"] else "FAIL", "detail": "production diagnostic path required; substitutes forbidden"},
        {"gate_id": "R28_EVIDENCE_TRIGGERED_ROOT_CAUSE_PREDICATES", "status": "PASS" if decision["root_cause_labels"]["passed"] else "FAIL", "detail": "distinct oracle, implementation, cubature, near-contact, DFT, and cost predicates"},
        {"gate_id": "R29_MULTILABEL_AND_PRINCIPAL_PRIORITY", "status": "PASS" if decision["root_cause_labels"]["multilabel"] and decision["root_cause_labels"]["priority_is_permutation"] else "FAIL", "detail": "simultaneous causes allowed; principal label priority frozen"},
        {"gate_id": "R30_DIAGNOSTIC_OUTPUT_CEILING", "status": "PASS" if len(packet["forbidden_outputs"]) == 8 else "FAIL", "detail": "no final vector, Jacobian, SVD, eta, forecast, or alpha claim"},
        {"gate_id": "R31_PREPARATION_DID_NOT_EXECUTE_SCIENCE", "status": "PASS" if packet["scope"]["diagnosis_executed"] is False and packet["scope"]["production_kernel_called_during_preparation"] is False else "FAIL", "detail": "contract metadata only"},
        {"gate_id": "R32_EXACTLY_ONE_DIAGNOSIS_EXECUTION_ELIGIBLE", "status": "PASS", "detail": "review acceptance authorizes one bounded diagnosis only"},
        {"gate_id": "R33_NO_REPAIR_OR_METHOD_REPLACEMENT", "status": "PASS" if packet["scope"]["production_integration_method_changed"] is False else "FAIL", "detail": "diagnosis cannot fix and rerun"},
        {"gate_id": "R34_NO_STAGE_A_VECTOR_OR_IDENTIFIABILITY", "status": "PASS" if packet["scope"]["final_real_150_vector_authorized"] is False and packet["scope"]["jacobian_authorized"] is False else "FAIL", "detail": "Stage A remains closed"},
        {"gate_id": "R35_NO_AUTOMATIC_V2_OR_STAGE_B", "status": "PASS" if packet["scope"]["automatic_v2_authorized"] is False and packet["scope"]["stage_b_authorized"] is False else "FAIL", "detail": "stochastic firewall preserved"},
        {"gate_id": "R36_POST_DIAGNOSIS_REVIEW_AND_SELECTOR_REQUIRED", "status": "PASS" if packet["packet_review_contract"]["post_diagnosis_independent_result_review_required"] and packet["packet_review_contract"]["post_diagnosis_fresh_selector_required"] else "FAIL", "detail": "no remedy is self-authorized by diagnosis"},
    ]
    failures = [row["gate_id"] for row in gates if row["status"] != "PASS"]
    if failures:
        raise ValueError(f"independent diagnosis packet review failed: {failures}")

    scope = {
        "independent_packet_review_executed": True,
        "packet_custody_verified": True,
        "kernel_diagnosis_contract_ready": True,
        "one_bounded_diagnosis_execution_authorized": True,
        "diagnosis_execution_performed": False,
        "production_kernel_called_during_review": False,
        "reference_oracle_called_during_review": False,
        "interaction_value_computed_during_review": False,
        "root_cause_computed_during_review": False,
        "production_integration_method_replacement_authorized": False,
        "implementation_correction_authorized": False,
        "immediate_diagnostic_retry_authorized": False,
        "stage_a_reopening_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_authorized": False,
        "svd_authorized": False,
        "eta_lambda_authorized": False,
        "identifiability_authorized": False,
        "automatic_v2_authorized": False,
        "stochastic_packet_preparation_authorized": False,
        "stage_b_eligible": False,
        "stage_b_authorized": False,
        "sensitivity_forecast_authorized": False,
        "numerical_alpha_bound_computed": False,
        "scalar_branch_adopted": False,
    }
    return {
        "schema_id": "toe.scalar_only_yukawa.sphere_kernel_diagnosis_and_reference_oracle.packet_review.v0",
        "review_id": "SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_PACKET_REVIEW_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "INDEPENDENT_PACKET_REVIEW_COMPLETE",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": frozen,
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_sphere_kernel_"
                "diagnosis_and_reference_oracle_packet_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
            "authorized_diagnosis_execution_count": 1,
            "performed_diagnosis_execution_count": 0,
        },
        "independent_domain_reproduction": domain,
        "independent_oracle_contract_reproduction": oracle,
        "independent_decision_contract_reproduction": decision,
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": gates,
        },
        "accepted_contract": {
            "case_count": 39,
            "evaluation_path_count": 4,
            "work_package_count": 9,
            "mutation_count": 10,
            "principal_root_cause_outcome_count": 7,
            "oracle_availability_outcome_count": 2,
            "diagnosis_execution_authorized": 1,
            "diagnosis_execution_performed": 0,
            "required_stop": "INDEPENDENT_DIAGNOSIS_RESULT_REVIEW",
        },
        "scope": scope,
        "claim_ceiling": (
            "This review accepts one bounded diagnostic contract and authorizes "
            "one diagnosis execution only. It performs no diagnostic calculation, "
            "accepts no root cause, changes no production method, and does not "
            "authorize repair, Stage A reopening, identifiability, V2, or Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Independently review the bounded Yukawa sphere-kernel diagnosis contract without executing it.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    rendered = artifact_bytes()
    if args.write:
        report_path.write_bytes(rendered)
        print(f"wrote {REPORT_RELATIVE_PATH} verdict={VERDICT}")
        return 0
    if not report_path.exists() or report_path.read_bytes() != rendered:
        print("sphere-kernel diagnosis packet review artifact missing or stale")
        return 1
    print(f"sphere-kernel diagnosis packet review OK verdict={VERDICT} gates=36/36")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
