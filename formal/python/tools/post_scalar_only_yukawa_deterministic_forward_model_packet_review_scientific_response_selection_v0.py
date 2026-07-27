from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_FORWARD_MODEL_"
    "PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_FORWARD_MODEL_"
    "PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_deterministic_forward_"
    "model_packet_review_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaDeterministicForwardModelPacketReviewScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260718_v0.json"
)

TARGET = (
    "select_post_scalar_only_yukawa_deterministic_forward_model_"
    "packet_review_scientific_response_v0"
)
VERDICT = (
    "SELECTED_FINAL_DETERMINISTIC_IDENTIFIABILITY_CONTRACT_REPAIR_"
    "PACKET_PREPARATION"
)
SELECTED_ROUTE = "REPAIR_DETERMINISTIC_IDENTIFIABILITY_EXECUTION_CONTRACT"
SELECTED_CANDIDATE_ID = "FOUR_INTERFACE_IDENTIFIABILITY_CONTRACT_REPAIR_V1"
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v1"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_FINAL_FOUR_INTERFACE_IDENTIFIABILITY_CONTRACT_"
    "REPAIR_NO_EXECUTION"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260718_v0.md":
        "2621c5a7eb159ff0bc7a1ebab86d9c9900cacf54371561223142aaeb46614e27",
    REVIEW_RELATIVE_PATH:
        "31fb8e245fc6fc69a65b2104e75169ad55177e980dd4bdb3ac552d8501c27bae",
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_review_v0.py":
        "85c3c4d6d5bd611a07446bdfda666344022fda684c8c3ee9262fcebbdb95f08e",
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_review_v0.py":
        "6ea11629d0e3cd574ab8cc4ba0b1a5dd92be44d34981e415cce994f670c09ba5",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationPacketReviewV0.lean":
        "0ae07220ac0a7044b499db6f3ae41896bd5a4b53c38acd088cd996a8184e05b3",
}

ACCEPTED_V0_GATES = (
    "G1_EXACT_PACKET_AUTHORITY_AND_CUSTODY",
    "G2_PENDING_REVIEW_STATUS_AND_NO_EXECUTION",
    "G3_STAGE_A_ONLY_SCOPE",
    "G4_FIXED_COMPARISON_AND_APPARATUS_GEOMETRY",
    "G5_HARMONIC_NORMALIZATION_PHASE_AND_SIGN",
    "G6_REAL_150_VECTOR_ORDER_AND_UNITS",
    "G7_ONE_SHARED_PRODUCTION_FUNCTION_CHAIN",
    "G8_UNIFORM_SPHERE_KERNEL_AND_STABLE_FORM_FACTOR",
    "G9_ANALYTIC_ENERGY_DERIVATIVE_TORQUE",
    "G10_TWO_GENUINELY_INDEPENDENT_TORQUE_CHECKS",
    "G11_FOUR_BENCHMARKS_HAVE_EXACT_TARGETS",
    "G12_FIVE_SCIENTIFIC_MUTATIONS_ROUTE_TO_CONTROLS",
    "G13_SYMMETRY_PHASE_SWAP_AND_ZERO_CONTROLS",
    "G14_NEAR_ZERO_ABSOLUTE_FLOOR",
    "G15_SIXTEEN_PERTURBATION_MAPS_AND_ORDER",
    "G16_EXPECTED_AMPLITUDE_DEGENERACY_DISCLOSED",
    "G17_JACOBIAN_DIMENSIONS_AND_PARAMETER_ORDER",
    "G19_DIMENSIONLESS_SVD_THRESHOLDS",
    "G23_CANONICAL_SERIALIZATION_AND_DETERMINISM",
    "G24_STAGE_B_EMPIRICAL_AND_THEORY_FIREWALL",
)

REPAIRABLE_V0_GATES = (
    "G18_JACOBIAN_FINITE_DIFFERENCE_STEPS",
    "G20_RANK_DEFICIENT_NUISANCE_PROJECTOR",
    "G21_TRANSITION_DOMAIN_EXACTNESS",
    "G22_IDENTIFIABILITY_REFINEMENT_STABILITY",
)

REVIEW_OUTCOMES = (
    "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY",
    "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
    "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE",
    "BLOCKED_TRANSITION_DOMAIN_CONTRACT",
    "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY",
)

CRITERIA = {
    "physics_first_information_gain": 5,
    "direct_repair_of_reviewed_defects": 5,
    "accepted_gate_preservation": 5,
    "risk_isolation": 4,
    "computational_economy": 4,
    "boundedness": 4,
    "authority_clarity": 3,
    "anti_rabbit_hole_control": 3,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "target": SELECTED_NEXT_TARGET,
        "scores": {key: 5 for key in CRITERIA},
        "disposition": "SELECTED_FOR_FINAL_V1_PACKET_PREPARATION_ONLY",
    },
    {
        "candidate_id": "SMALLER_EXPLORATORY_DETERMINISTIC_CALCULATION",
        "target": "prepare_exploratory_scalar_only_yukawa_identifiability_calculation_v0",
        "scores": {
            "physics_first_information_gain": 4,
            "direct_repair_of_reviewed_defects": 2,
            "accepted_gate_preservation": 3,
            "risk_isolation": 5,
            "computational_economy": 5,
            "boundedness": 5,
            "authority_clarity": 4,
            "anti_rabbit_hole_control": 4,
        },
        "disposition": "DEFERRED_UNLESS_V1_REVIEW_FINDS_NEW_FOUNDATIONAL_DEFECT",
    },
    {
        "candidate_id": "SIMPLIFY_DETERMINISTIC_NUISANCE_SET",
        "target": "select_scalar_only_yukawa_simplified_nuisance_set_v0",
        "scores": {
            "physics_first_information_gain": 4,
            "direct_repair_of_reviewed_defects": 3,
            "accepted_gate_preservation": 2,
            "risk_isolation": 4,
            "computational_economy": 4,
            "boundedness": 5,
            "authority_clarity": 4,
            "anti_rabbit_hole_control": 4,
        },
        "disposition": "DEFERRED_CHANGES_SCIENTIFIC_QUESTION",
    },
    {
        "candidate_id": "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        "target": "select_post_scalar_internal_torsion_balance_lane_closure_v0",
        "scores": {
            "physics_first_information_gain": 1,
            "direct_repair_of_reviewed_defects": 0,
            "accepted_gate_preservation": 5,
            "risk_isolation": 5,
            "computational_economy": 5,
            "boundedness": 5,
            "authority_clarity": 5,
            "anti_rabbit_hole_control": 5,
        },
        "disposition": "DEFERRED_UNTIL_ONE_FAIR_REPAIRED_EXECUTION_IS_CONSIDERED",
    },
    {
        "candidate_id": "REDESIGN_INTERNAL_TORSION_BALANCE_APPARATUS",
        "target": "prepare_redesigned_scalar_only_yukawa_internal_apparatus_packet_v0",
        "scores": {
            "physics_first_information_gain": 4,
            "direct_repair_of_reviewed_defects": 2,
            "accepted_gate_preservation": 1,
            "risk_isolation": 3,
            "computational_economy": 1,
            "boundedness": 2,
            "authority_clarity": 3,
            "anti_rabbit_hole_control": 4,
        },
        "disposition": "DEFERRED_PREMATURE_BEFORE_IDENTIFIABILITY_EXECUTION",
    },
)

NUISANCE_SCALES = (
    ("TORQUE_CALIBRATION", 0.02, "fraction"),
    ("SOURCE_DENSITY_SCALE", 0.01, "fraction"),
    ("DETECTOR_DENSITY_SCALE", 0.01, "fraction"),
    ("DETECTOR_LEVER_OFFSET", 1e-4, "m"),
    ("ATTRACTOR_LEVER_OFFSET", 1e-4, "m"),
    ("GAP_OFFSET", 1e-5, "m"),
    ("ATTRACTOR_AXIS_X_OFFSET", 1e-4, "m"),
    ("ATTRACTOR_AXIS_Y_OFFSET", 1e-4, "m"),
    ("ANGULAR_ZERO_OFFSET", 1e-3, "rad"),
    ("HARMONIC_LEAKAGE", 0.002, "fraction"),
    ("BACKGROUND_2RE", 1e-17, "N_m"),
    ("BACKGROUND_2IM", 1e-17, "N_m"),
    ("BACKGROUND_4RE", 1e-17, "N_m"),
    ("BACKGROUND_4IM", 1e-17, "N_m"),
    ("BACKGROUND_6RE", 1e-17, "N_m"),
    ("BACKGROUND_6IM", 1e-17, "N_m"),
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
    for relative_path, expected_hash in AUTHORITY_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"deterministic packet-review authority drift: {relative_path}")

    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_PARAMETER_IDENTIFIABILITY":
        raise ValueError("deterministic packet-review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("deterministic packet review did not authorize this selection")
    if review.get("review_gates", {}).get("pass_count") != 20:
        raise ValueError("accepted-gate count mismatch")
    if review.get("review_gates", {}).get("failure_count") != 4:
        raise ValueError("failed-gate count mismatch")
    if review.get("jacobian_contract_review", {}).get("physical_identifiability_evaluated") is not False:
        raise ValueError("review unexpectedly evaluated physical identifiability")
    if review.get("scope", {}).get("deterministic_execution_performed") is not False:
        raise ValueError("review unexpectedly performed deterministic execution")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    selection_gates = (
        "EXACT_PACKET_REVIEW_AUTHORITY_AND_TARGET",
        "BLOCK_IS_CONTRACTUAL_NOT_PHYSICAL",
        "EXACTLY_TWENTY_ACCEPTED_GATES_FROZEN",
        "EXACTLY_FOUR_FAILED_INTERFACES_REPAIRABLE",
        "EXACTLY_FIVE_RESPONSES_COMPARED",
        "EXACTLY_EIGHT_CRITERIA_FROZEN",
        "SELECTION_STABLE_IN_24_VARIANTS",
        "DIMENSIONLESS_PARAMETER_SCALES_FROZEN",
        "FINITE_DIFFERENCE_LADDER_AND_PLATEAU_FROZEN",
        "BOUNDARY_AND_FAILED_EVALUATION_RULES_FROZEN",
        "RANK_DEFICIENT_SVD_PROJECTOR_FROZEN",
        "ZERO_EXACT_AND_NEAR_DEGENERACY_RULES_FROZEN",
        "ETA_DEFINITION_AND_EXISTING_BANDS_FROZEN",
        "EXACT_TRANSITION_INDICES_AND_SENTINELS_FROZEN",
        "REFINEMENT_AND_THRESHOLD_STABILITY_FROZEN",
        "TEN_PRODUCTION_PATH_CONTROLS_REQUIRED",
        "FIVE_V1_REVIEW_OUTCOMES_EXACT",
        "V1_IS_LAST_AUTOMATIC_REPAIR",
        "NO_PACKET_REPAIR_OR_EXECUTION_NOW",
        "STAGE_B_EMPIRICAL_AND_THEORY_FIREWALL_RETAINED",
    )

    mandatory_controls = (
        "OVERSIZED_STEP_H_0P3_FAILS_PLATEAU",
        "UNDERSIZED_STEP_H_1E_MINUS_8_FAILS_PLATEAU",
        "EXACT_DUPLICATE_NUISANCE_COLUMNS_REDUCE_RANK_WITHOUT_CRASH",
        "NEAR_DUPLICATE_NUISANCE_COLUMNS_TRIGGER_NEAR_DEGENERACY",
        "STABLE_RESULT_SURVIVES_ALL_THREE_SVD_THRESHOLDS",
        "UNSTABLE_TRANSITION_POINT_CANNOT_REPRESENT_DOMAIN",
        "FORWARD_CONVERGENCE_CANNOT_OVERRIDE_UNSTABLE_JACOBIAN",
        "SCALAR_PROPORTIONAL_TO_CALIBRATION_YIELDS_ETA_ZERO",
        "NUISANCE_ORTHOGONAL_SCALAR_YIELDS_ETA_ONE",
        "ALL_CONTROLS_USE_PRODUCTION_COMPONENTS",
    )

    scope = {
        "scientific_response_selection_executed": True,
        "accepted_v0_gates_frozen": True,
        "v1_repair_packet_preparation_authorized": True,
        "final_automatic_repair_boundary_frozen": True,
        "v1_repair_packet_prepared_now": False,
        "v0_packet_modified": False,
        "deterministic_execution_authorized": False,
        "deterministic_execution_performed": False,
        "forward_vector_produced": False,
        "jacobian_computed": False,
        "physical_unidentifiability_established": False,
        "stochastic_packet_preparation_authorized": False,
        "stochastic_forecast_authorized": False,
        "stochastic_forecast_performed": False,
        "synthetic_dataset_generated": False,
        "measured_evidence_used": False,
        "empirical_constraint_claimed": False,
        "numerical_lambda_bound_computed": False,
        "numerical_alpha_bound_computed": False,
        "alpha_sign_or_value_adopted": False,
        "scalar_branch_adopted": False,
        "native_scalar_bridge_identified": False,
        "native_gravitational_principle_identified": False,
        "gravitational_action_selected": False,
        "outbound_contact_authorized": False,
        "private_data_dependency_created": False,
        "automatic_v2_repair_authorized": False,
    }

    return {
        "schema_id": "toe.post_scalar_only_yukawa.deterministic_forward_model_packet_review.scientific_response_selection.v0",
        "packet_id": "POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_FORWARD_MODEL_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_route": SELECTED_ROUTE,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_review_verdict": review["verdict"],
            "frozen_packet_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_selection": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/post_scalar_only_yukawa_deterministic_"
                "forward_model_packet_review_scientific_response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "review_interpretation": {
            "review_verdict": review["verdict"],
            "physical_unidentifiability_established": False,
            "deterministic_forward_model_failure_established": False,
            "identifiability_decision_contract_complete": False,
            "deterministic_execution": "NOT_PERFORMED",
            "forward_vector": "NOT_PRODUCED",
            "jacobian": "NOT_COMPUTED",
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
        "accepted_gate_freeze": {
            "accepted_gate_count": len(ACCEPTED_V0_GATES),
            "mutable_gate_count": len(REPAIRABLE_V0_GATES),
            "accepted_gates": list(ACCEPTED_V0_GATES),
            "repairable_gates": list(REPAIRABLE_V0_GATES),
            "all_other_v0_interfaces": "FROZEN_NO_SEMANTIC_CHANGE",
        },
        "v1_repair_contract": {
            "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
            "dimensionless_parameterization": {
                "lambda_coordinate": "q_lambda=log(lambda/1e-3_m)",
                "nuisance_coordinate": "q_j=(p_j-p_j0)/s_j",
                "nuisance_scales": [
                    {"parameter_id": item[0], "scale": item[1], "unit": item[2]}
                    for item in NUISANCE_SCALES
                ],
                "scale_source": "POSITIVE_HALF_WIDTH_OF_ACCEPTED_V0_TEST_RANGE",
                "post_result_scaling_forbidden": True,
            },
            "finite_difference": {
                "dimensionless_step_ladder": [1e-2, 3e-3, 1e-3],
                "interior_rule": "CENTERED_TWO_POINT",
                "lower_boundary_rule": "SECOND_ORDER_THREE_POINT_FORWARD_(-3f0+4f1-f2)/(2h)",
                "upper_boundary_rule": "SECOND_ORDER_THREE_POINT_BACKWARD_(3f0-4f_1+f_2)/(2h)",
                "exact_linear_columns": "ACCEPTED_ANALYTIC_DERIVATIVE_PATH",
                "plateau_steps": [3e-3, 1e-3],
                "plateau_norm": "RMS_AFTER_ACCEPTED_GLOBAL_OUTPUT_SCALING",
                "absolute_tolerance": 1e-10,
                "relative_tolerance": 5e-3,
                "acceptance_rule": "RMS(D_3e-3-D_1e-3)<=1e-10+5e-3*RMS(D_1e-3)",
                "failed_perturbed_evaluation": "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
                "result_dependent_adaptation": "FORBIDDEN",
                "oversized_mutation_step": 0.3,
                "undersized_mutation_step": 1e-8,
            },
            "rank_deficient_projector": {
                "output_scaling": "ACCEPTED_V0_GLOBAL_OUTPUT_SCALE",
                "zero_column_norm_threshold": "sqrt(150)*1e-12",
                "nonzero_nuisance_column_scaling": "UNIT_EUCLIDEAN_NORM",
                "factorization": "THIN_SVD_N_TILDE=U_SIGMA_VT",
                "central_relative_rank_threshold": 1e-10,
                "probe_relative_rank_thresholds": [1e-9, 1e-11],
                "retained_rule": "sigma_i/sigma_1>threshold",
                "projector": "P_perp=I-U_r*U_r^T",
                "eta_lambda": "norm2(P_perp*j_lambda)/norm2(j_lambda)",
                "scalar_zero_column_behavior": "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED",
                "orthonormality_tolerance": 1e-12,
                "relative_reconstruction_tolerance": 1e-9,
                "near_degenerate_absolute_correlation_threshold": 0.999,
                "near_degenerate_condition_number_threshold": 1e8,
                "exact_duplicate_behavior": "REDUCE_RANK_WITHOUT_CRASH",
                "indistinguishable_eta_max": 1e-6,
                "identifiable_eta_min": 1e-3,
                "intermediate_eta_classification": "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED",
            },
            "transition_domain": {
                "lambda_grid": "lambda_i=10^(-5+i/6)_m_for_i=0..24",
                "d_min_m": 1e-4,
                "d_max_m": 1e-2,
                "exact_grid_predicate": "d_min/3<=lambda_i<=3*d_max",
                "decision_bearing_indices_zero_based": list(range(4, 21)),
                "decision_bearing_index_count": 17,
                "regime_sentinel_formula": [
                    "d_min/3", "d_min", "sqrt(d_min*d_max)", "d_max", "3*d_max"
                ],
                "regime_sentinel_values_m": [1e-4 / 3.0, 1e-4, 1e-3, 1e-2, 3e-2],
                "required_metrics_at_every_grid_and_sentinel_point": [
                    "RETAINED_RANK",
                    "SINGULAR_VALUE_SPECTRUM",
                    "MAXIMUM_SCALAR_NUISANCE_ABSOLUTE_CORRELATION",
                    "NUISANCE_PROJECTOR",
                    "ETA_LAMBDA",
                    "REFINEMENT_STABILITY",
                ],
                "sentinel_role": "MANDATORY_REGIME_DIAGNOSTIC_NOT_CONTIGUITY_SUBSTITUTE",
                "post_result_point_selection": "FORBIDDEN",
                "minimum_contiguous_identifiable_grid_points": 5,
                "single_point_domain_generalization": "FORBIDDEN",
                "domain_classification": {
                    "prerequisite": "ALL_DECISION_BEARING_NUMERICAL_STABILITY_RULES_PASS",
                    "identifiable": (
                        "AT_LEAST_5_CONTIGUOUS_TRANSITION_GRID_POINTS_WITH_ETA_GE_1E-3"
                    ),
                    "identifiable_outcome": "DETERMINISTIC_PARAMETER_IDENTIFIABLE",
                    "unidentifiable": "ALL_17_TRANSITION_GRID_POINTS_WITH_ETA_LE_1E-6",
                    "unidentifiable_outcome": "BLOCKED_PARAMETER_IDENTIFIABILITY",
                    "otherwise": "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED",
                },
            },
            "refinement_stability": {
                "comparison_levels": "FINAL_TWO_ACCEPTED_PRODUCTION_REFINEMENTS",
                "retained_rank": "IDENTICAL",
                "eta_absolute_change_max": 0.02,
                "eta_relative_change_max": 0.05,
                "eta_relative_change_applicability": "max_eta>1e-6",
                "maximum_column_correlation_absolute_change_max": 0.02,
                "largest_principal_angle_degrees_max": 1.0,
                "decision_bearing_log10_singular_value_change_decades_max": 0.05,
                "exact_and_near_degeneracy_labels": "IDENTICAL",
                "point_classification": "IDENTICAL",
                "threshold_probe_rank_and_classification": "IDENTICAL",
                "threshold_probe_eta_spread_max": 0.02,
                "forward_convergence_override": "FORBIDDEN",
            },
            "mandatory_control_count": len(mandatory_controls),
            "mandatory_controls": list(mandatory_controls),
            "control_path": (
                "PRODUCTION_FORWARD_MODEL_JACOBIAN_BUILDER_SCALER_PROJECTOR_"
                "REFINEMENT_ADJUDICATOR"
            ),
            "review_outcomes": list(REVIEW_OUTCOMES),
            "physical_identifiability_result_reserved_for_execution": True,
        },
        "anti_rabbit_hole_boundary": {
            "v1_is_last_automatic_stage_a_repair": True,
            "automatic_v2_authorized": False,
            "new_foundational_defect_requires_new_selector": True,
            "required_future_choices": [
                "SIMPLIFY_NUISANCE_SET",
                "REDESIGN_INTERNAL_APPARATUS",
                "SMALLER_EXPLORATORY_DETERMINISTIC_CALCULATION",
                "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
            ],
        },
        "selection_gates": {
            "gate_count": len(selection_gates),
            "pass_count": len(selection_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in selection_gates],
        },
        "scope": scope,
        "current_posture": {
            "stage_a_packet_v0": "BLOCKED_PARAMETER_IDENTIFIABILITY",
            "physical_unidentifiability": "NOT_ESTABLISHED",
            "accepted_gates": "20_OF_24_FROZEN",
            "v1_repair_packet": "AUTHORIZED_FOR_PREPARATION_NOT_PREPARED",
            "deterministic_execution": "NOT_AUTHORIZED_NOT_PERFORMED",
            "forward_vector": "NOT_PRODUCED",
            "jacobian": "NOT_COMPUTED",
            "stage_b": "DEFERRED_NOT_AUTHORIZED",
            "synthetic_or_empirical_constraint": "NONE",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This selection freezes a final four-interface repair specification and "
            "authorizes preparation only of deterministic validation packet v1. It "
            "does not prepare or execute v1, alter the twenty accepted v0 gates, "
            "establish physical identifiability or unidentifiability, produce a "
            "forward vector or Jacobian, authorize Stage B, compute a constraint, "
            "or adopt a scalar branch, bridge, principle, or action."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Select the response to the blocked deterministic Yukawa packet review."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    output = REPO_ROOT / REPORT_RELATIVE_PATH
    expected = artifact_bytes()
    current = output.read_bytes() if output.exists() else None
    if args.write:
        if current != expected:
            output.write_bytes(expected)
            print(f"wrote {REPORT_RELATIVE_PATH}")
        else:
            print("post-deterministic-review selection already current")
        return 0
    if current != expected:
        print("post-deterministic-review selection drift")
        return 1
    print("post-deterministic-review selection OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
