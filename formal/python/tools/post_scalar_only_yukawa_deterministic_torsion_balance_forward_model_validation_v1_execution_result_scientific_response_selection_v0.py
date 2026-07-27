from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_V1_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_V1_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_deterministic_torsion_"
    "balance_forward_model_validation_v1_execution_result_scientific_response_"
    "selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationV1"
    "ExecutionResultScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_EXECUTION_RESULT_REVIEW_20260719_v1.json"
)

TARGET = (
    "select_post_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1_execution_result_scientific_response_v0"
)
VERDICT = (
    "SELECTED_BOUNDED_PRODUCTION_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_"
    "PACKET_PREPARATION"
)
SELECTED_ROUTE = "BOUNDED_PRODUCTION_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE"
SELECTED_CANDIDATE_ID = "SPHERE_KERNEL_DIAGNOSIS_AND_INDEPENDENT_REFERENCE_ORACLE"
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_yukawa_sphere_kernel_diagnosis_and_"
    "reference_oracle_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_BOUNDED_KERNEL_DIAGNOSIS_PACKET_NO_FORWARD_MODEL_RERUN"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_RESULT_REVIEW_20260719_v1.md":
        "0c7c8ef681de18988f6e589baefc9f40c89fb6a0b70bf2b3d870fb98ab790fbd",
    REVIEW_RELATIVE_PATH:
        "c6a7278025714753144e429d47fe065eb8a40bdd8d45e3f609a25c0ffd6aa968",
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_execution_result_review_v1.py":
        "51f3a90eba53d334e557eab151056b8ca11e50100317628300dd8c59f092a6ab",
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_execution_result_review_v1.py":
        "9f7712f345bef3b150511105a3a6804dd380b7a0195f7001f0f654aa94974e4c",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationExecutionResultReviewV1.lean":
        "4b87df200686ea257b78cb2060e57ca3047bf13a48ac359aadfcc9ec94db9bd5",
}

CRITERIA = {
    "root_cause_information_gain": 5,
    "direct_response_to_accepted_failure": 5,
    "independent_oracle_strength": 5,
    "method_selection_value": 4,
    "accepted_result_and_contract_preservation": 4,
    "boundedness_and_no_rerun": 5,
    "computational_economy": 3,
    "anti_rabbit_hole_exit_clarity": 4,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "route": SELECTED_ROUTE,
        "target": SELECTED_NEXT_TARGET,
        "scores": {
            "root_cause_information_gain": 5,
            "direct_response_to_accepted_failure": 5,
            "independent_oracle_strength": 5,
            "method_selection_value": 5,
            "accepted_result_and_contract_preservation": 5,
            "boundedness_and_no_rerun": 5,
            "computational_economy": 4,
            "anti_rabbit_hole_exit_clarity": 5,
        },
        "disposition": "SELECTED_FOR_BOUNDED_DIAGNOSIS_PACKET_PREPARATION",
    },
    {
        "candidate_id": "REPLACE_PRODUCTION_INTEGRATION_METHOD",
        "route": "DIRECT_INTEGRATION_METHOD_REPLACEMENT",
        "target": "prepare_scalar_only_yukawa_replacement_extended_body_kernel_packet_v0",
        "scores": {
            "root_cause_information_gain": 3,
            "direct_response_to_accepted_failure": 5,
            "independent_oracle_strength": 4,
            "method_selection_value": 2,
            "accepted_result_and_contract_preservation": 3,
            "boundedness_and_no_rerun": 3,
            "computational_economy": 3,
            "anti_rabbit_hole_exit_clarity": 3,
        },
        "disposition": "DEFERRED_PENDING_ROOT_CAUSE_AND_ORACLE_DIAGNOSIS",
    },
    {
        "candidate_id": "SIMPLIFY_OR_REDESIGN_APPARATUS",
        "route": "APPARATUS_SIMPLIFICATION_OR_REDESIGN",
        "target": "prepare_redesigned_scalar_only_yukawa_internal_apparatus_packet_v0",
        "scores": {
            "root_cause_information_gain": 2,
            "direct_response_to_accepted_failure": 3,
            "independent_oracle_strength": 3,
            "method_selection_value": 2,
            "accepted_result_and_contract_preservation": 1,
            "boundedness_and_no_rerun": 3,
            "computational_economy": 2,
            "anti_rabbit_hole_exit_clarity": 4,
        },
        "disposition": "DEFERRED_PREMATURE_BEFORE_KERNEL_DIAGNOSIS",
    },
    {
        "candidate_id": "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        "route": "CLOSE_INTERNAL_SYNTHETIC_TORSION_BALANCE_LANE",
        "target": "select_post_scalar_internal_torsion_balance_lane_closure_v0",
        "scores": {
            "root_cause_information_gain": 0,
            "direct_response_to_accepted_failure": 0,
            "independent_oracle_strength": 0,
            "method_selection_value": 0,
            "accepted_result_and_contract_preservation": 5,
            "boundedness_and_no_rerun": 5,
            "computational_economy": 5,
            "anti_rabbit_hole_exit_clarity": 5,
        },
        "disposition": "DEFERRED_UNTIL_ONE_BOUNDED_DIAGNOSIS_IS_CONSIDERED",
    },
)

ROOT_CAUSE_OUTCOMES = (
    "IMPLEMENTATION_DEFECT_LOCALIZED",
    "FIXED_ORDER_CUBATURE_INADEQUATE",
    "REFERENCE_ORACLE_INADEQUATE",
    "NEAR_CONTACT_DOMAIN_DECOMPOSITION_REQUIRED",
    "ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE",
    "KERNEL_NOISE_DRIVES_DFT_FAILURE",
    "INTERNAL_APPARATUS_FORWARD_MODEL_NOT_ECONOMICALLY_VALIDATABLE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _weighted_score(scores: dict[str, int], weights: dict[str, int]) -> int:
    if set(scores) != set(weights):
        raise ValueError("candidate score criteria mismatch")
    return sum(scores[key] * weights[key] for key in weights)


def _rank(weights: dict[str, int]) -> list[dict[str, Any]]:
    rows = []
    for candidate in CANDIDATES:
        row = dict(candidate)
        row["weighted_score"] = _weighted_score(candidate["scores"], weights)
        rows.append(row)
    return sorted(rows, key=lambda row: (-row["weighted_score"], row["candidate_id"]))


def _sensitivity() -> dict[str, Any]:
    rows = []
    for omitted in CRITERIA:
        weights = dict(CRITERIA)
        weights[omitted] = 0
        ranked = _rank(weights)
        rows.append({
            "variant": f"omit_{omitted}",
            "selected_candidate_id": ranked[0]["candidate_id"],
            "selected_score": ranked[0]["weighted_score"],
            "runner_up_candidate_id": ranked[1]["candidate_id"],
            "runner_up_score": ranked[1]["weighted_score"],
        })
    for criterion, baseline in CRITERIA.items():
        for delta in (-1, 1):
            weights = dict(CRITERIA)
            weights[criterion] = max(1, baseline + delta)
            ranked = _rank(weights)
            rows.append({
                "variant": f"{criterion}_{delta:+d}",
                "selected_candidate_id": ranked[0]["candidate_id"],
                "selected_score": ranked[0]["weighted_score"],
                "runner_up_candidate_id": ranked[1]["candidate_id"],
                "runner_up_score": ranked[1]["weighted_score"],
            })
    return {
        "variant_count": len(rows),
        "rows": rows,
        "selected_candidate_stable_in_all_variants": all(
            row["selected_candidate_id"] == SELECTED_CANDIDATE_ID for row in rows
        ),
        "minimum_winning_margin": min(
            row["selected_score"] - row["runner_up_score"] for row in rows
        ),
    }


def build_report() -> dict[str, Any]:
    for relative_path, expected in AUTHORITY_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"execution-result-review authority drift: {relative_path}")
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_PRODUCTION_KERNEL_VALIDATION":
        raise ValueError("accepted execution-result-review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("execution result review did not authorize this selector")
    if review.get("review_gates", {}).get("pass_count") != 11:
        raise ValueError("independent result-review gate count mismatch")
    if review.get("scope", {}).get("physical_identifiability_evaluated") is not False:
        raise ValueError("result review unexpectedly evaluated physical identifiability")
    if review.get("scope", {}).get("stage_b_authorized") is not False:
        raise ValueError("result review unexpectedly authorized Stage B")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("declared selector winner does not match ranking")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("selector winner is not stable under frozen sensitivity probes")

    selection_gates = (
        "EXACT_ACCEPTED_RESULT_REVIEW_AUTHORITY_AND_TARGET",
        "BLOCK_IS_NUMERICAL_KERNEL_VALIDATION_NOT_PHYSICAL_UNIDENTIFIABILITY",
        "EXACTLY_FOUR_BOUNDED_RESPONSES_COMPARED",
        "EXACTLY_EIGHT_SELECTION_CRITERIA_FROZEN",
        "DIAGNOSIS_ROUTE_RANKS_FIRST",
        "SELECTION_STABLE_IN_24_WEIGHT_VARIANTS",
        "DIAGNOSIS_PRECEDES_METHOD_REPLACEMENT",
        "NEWTONIAN_AND_YUKAWA_COMPONENTS_SEPARATED",
        "GENUINELY_INDEPENDENT_REFERENCE_ORACLE_REQUIRED",
        "GAP_AND_RANGE_STRATA_MUST_BE_PREREGISTERED",
        "NEAR_CONTACT_LOCALIZATION_REQUIRED",
        "PRECISION_CANCELLATION_AND_SUMMATION_PROBES_REQUIRED",
        "ANALYTIC_SYNTHETIC_DFT_ISOLATION_REQUIRED",
        "ROOT_CAUSE_CLASSIFICATION_FROZEN",
        "DIAGNOSTIC_OUTPUTS_ONLY",
        "FINAL_REAL_150_VECTOR_JACOBIAN_AND_SVD_FORBIDDEN",
        "NO_FULL_FORWARD_MODEL_RERUN",
        "NO_AUTOMATIC_V2_OR_STAGE_B",
        "PACKET_PREPARATION_ONLY_NO_DIAGNOSIS_NOW",
        "FRESH_POST_DIAGNOSIS_SELECTOR_REQUIRED",
    )

    scope = {
        "scientific_response_selection_executed": True,
        "accepted_execution_result_frozen": True,
        "four_bounded_options_compared": True,
        "kernel_diagnosis_packet_preparation_authorized": True,
        "independent_reference_oracle_packet_preparation_authorized": True,
        "kernel_diagnosis_packet_prepared_now": False,
        "kernel_diagnosis_executed": False,
        "independent_reference_oracle_computed": False,
        "production_integration_method_replacement_authorized": False,
        "apparatus_redesign_authorized": False,
        "torsion_balance_lane_closure_authorized": False,
        "additional_deterministic_execution_authorized": False,
        "full_forward_model_rerun_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_authorized": False,
        "svd_authorized": False,
        "eta_lambda_authorized": False,
        "identifiability_classification_authorized": False,
        "stochastic_packet_preparation_authorized": False,
        "stage_b_eligible": False,
        "stage_b_authorized": False,
        "automatic_v2_authorized": False,
        "synthetic_dataset_authorized": False,
        "monte_carlo_authorized": False,
        "sensitivity_forecast_authorized": False,
        "empirical_constraint_claimed": False,
        "numerical_alpha_bound_computed": False,
        "scalar_branch_adopted": False,
    }

    return {
        "schema_id": "toe.post_scalar_only_yukawa.deterministic_torsion_balance_forward_model_validation_v1_execution_result.scientific_response_selection.v0",
        "packet_id": "POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_V1_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_route": SELECTED_ROUTE,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_result_review_verdict": review["verdict"],
            "frozen_result_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_selection": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/post_scalar_only_yukawa_deterministic_"
                "torsion_balance_forward_model_validation_v1_execution_result_"
                "scientific_response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "accepted_result_interpretation": {
            "principal_result": review["verdict"],
            "deterministic_apparatus_model": "NOT_VALIDATED",
            "apparatus_physically_unidentifiable": False,
            "physical_identifiability": "NOT_TESTED",
            "jacobian": "NOT_COMPUTED",
            "stage_b": "NOT_AUTHORIZED",
            "rerun": "NOT_AUTHORIZED",
            "localized_block": "EXTENDED_SOURCE_NUMERICAL_TRANSPORT_AND_HARMONIC_REFINEMENT",
        },
        "selection_policy": {
            "candidate_count": len(CANDIDATES),
            "criterion_count": len(CRITERIA),
            "criteria_weights": CRITERIA,
            "criterion_scale": "0_TO_5_PRIORITY_SCORE_NOT_TRUTH_PROBABILITY",
            "tie_break_rule": "LEXICOGRAPHIC_CANDIDATE_ID",
        },
        "ranking": {
            "rows": ranking,
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
            "winning_margin": ranking[0]["weighted_score"] - ranking[1]["weighted_score"],
        },
        "sensitivity_analysis": sensitivity,
        "diagnosis_packet_preparation_requirements": {
            "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
            "scientific_objective": (
                "Distinguish implementation defect, fixed-order method inadequacy, "
                "reference-oracle inadequacy, near-contact localization, and an "
                "independent angular-resolution failure without rerunning Stage A."
            ),
            "component_separation": {
                "required_components": ["NEWTONIAN", "YUKAWA"],
                "required_records": [
                    "ABSOLUTE_RESULT",
                    "RELATIVE_ERROR",
                    "CONVERGENCE_RECORD",
                    "DIMENSIONAL_CHECK",
                    "LIMITING_BEHAVIOR",
                ],
                "combined_total_cannot_substitute": True,
            },
            "reference_oracle": {
                "nearby_order_same_cubature_sufficient": False,
                "independent_route_required": True,
                "permitted_families": [
                    "INDEPENDENT_ANALYTIC_UNIFORM_SPHERE_RESULT",
                    "SEMI_ANALYTIC_REDUCED_DIMENSION_INTEGRAL",
                    "ADAPTIVE_HIGH_PRECISION_QUADRATURE",
                    "ARBITRARY_PRECISION_REFERENCE",
                    "INDEPENDENT_COORDINATE_OR_CONVOLUTION_TRANSFORM",
                ],
                "oracle_self_convergence_required": True,
                "oracle_tolerances_must_be_frozen_before_execution": True,
            },
            "gap_and_range_strata": {
                "lambda_regimes": ["LAMBDA_MUCH_LESS_THAN_GAP", "LAMBDA_COMPARABLE_TO_GAP", "LAMBDA_MUCH_GREATER_THAN_GAP"],
                "multiple_closest_surface_separations_required": True,
                "exact_grid_must_be_frozen_in_packet": True,
                "post_result_point_selection_forbidden": True,
            },
            "near_contact_diagnosis": {
                "minimum_separation_recorded": True,
                "local_kernel_variation_recorded": True,
                "subdomain_contributions_recorded": True,
                "adaptive_subdivision_resolution_tested": True,
                "tensor_product_node_efficiency_recorded": True,
            },
            "precision_and_cancellation": {
                "standard_vs_higher_precision": True,
                "separate_vs_combined_components": True,
                "stable_summation": True,
                "symmetry_reduction": True,
                "coordinate_scaling": True,
                "absolute_and_relative_error_rules": True,
            },
            "angular_dft_isolation": {
                "analytic_synthetic_torque_first": True,
                "known_harmonics": [2, 4, 6],
                "production_torque_test_after_kernel_accuracy_only": True,
                "distinguish_grid_resolution_from_kernel_noise": True,
            },
            "required_outputs": [
                "NEWTONIAN_KERNEL_ACCURACY",
                "YUKAWA_KERNEL_ACCURACY",
                "REFERENCE_ORACLE_CONVERGENCE",
                "ERROR_VS_INTEGRATION_RESOLUTION",
                "ERROR_VS_GAP_AND_SCALAR_RANGE",
                "ANALYTIC_AND_PRODUCTION_DFT_CONVERGENCE",
                "ROOT_CAUSE_CLASSIFICATION",
                "RECOMMENDED_NUMERICAL_METHOD",
                "ESTIMATED_COMPUTATIONAL_COST",
            ],
            "forbidden_outputs": [
                "FINAL_REAL_150_APPARATUS_VECTOR",
                "JACOBIAN",
                "SVD",
                "ETA_LAMBDA",
                "IDENTIFIABILITY_RESULT",
                "SYNTHETIC_NOISE",
                "SENSITIVITY_FORECAST",
            ],
            "root_cause_outcomes": list(ROOT_CAUSE_OUTCOMES),
            "execution_budget_and_stop_rules_must_be_frozen_in_packet": True,
        },
        "anti_rabbit_hole_boundary": {
            "full_stage_a_rerun_prohibited": True,
            "tolerance_relaxation_prohibited": True,
            "result_dependent_method_selection_prohibited": True,
            "automatic_v2_prohibited": True,
            "post_diagnosis_method_change_requires_fresh_selector": True,
            "post_diagnosis_full_execution_requires_fresh_packet_and_review": True,
        },
        "selection_gates": {
            "gate_count": len(selection_gates),
            "pass_count": len(selection_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in selection_gates],
        },
        "scope": scope,
        "claim_ceiling": (
            "This selector authorizes preparation of one bounded kernel-diagnosis "
            "and independent-reference-oracle packet only. It performs no diagnosis, "
            "changes no production method, reruns no Stage A calculation, produces "
            "no final vector or identifiability result, and does not authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Select the bounded response to the accepted Yukawa Stage A kernel block.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    rendered = artifact_bytes()
    if args.write:
        report_path.write_bytes(rendered)
        print(f"wrote {REPORT_RELATIVE_PATH} route={SELECTED_ROUTE}")
        return 0
    if not report_path.exists() or report_path.read_bytes() != rendered:
        print("post-execution scientific-response selector artifact missing or stale")
        return 1
    print(f"post-execution selector OK route={SELECTED_ROUTE} gates=20/20")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
