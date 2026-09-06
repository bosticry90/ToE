from __future__ import annotations

import argparse
import hashlib
import json
from copy import deepcopy
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_20260719_v1.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_20260719_v1.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v1.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationPacketV1.lean"
)
V0_PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_20260718_v0.json"
)
V0_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260718_v0.json"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_FORWARD_MODEL_"
    "PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)

TARGET = (
    "prepare_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v1"
)
VERDICT = (
    "PREPARED_FINAL_DETERMINISTIC_IDENTIFIABILITY_CONTRACT_REPAIR_"
    "PENDING_INDEPENDENT_REVIEW"
)
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v1_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_REVIEW_ONLY_NO_DETERMINISTIC_OR_STOCHASTIC_EXECUTION"
)
READY_EXECUTION_TARGET = (
    "execute_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1_once"
)
BLOCKED_REVIEW_RESPONSE_TARGET = (
    "select_post_scalar_only_yukawa_deterministic_identifiability_contract_"
    "v1_review_scientific_response_v0"
)

SELECTOR_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_FORWARD_MODEL_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md":
        "310a517c9348e5872c8ec2bbd89b1d065c38d07804ec2ba122dc61ec221e2451",
    SELECTOR_RELATIVE_PATH:
        "4c9771c89037a194ea123195d48102b738a85f05ab71bcf0d1905e4deec41bff",
    "formal/python/tools/post_scalar_only_yukawa_deterministic_forward_model_packet_review_scientific_response_selection_v0.py":
        "0771dd9130a16d69627b184f472745c2aad6972750a09eed2b8f2e1ea3f2198e",
    "formal/python/tests/test_post_scalar_only_yukawa_deterministic_forward_model_packet_review_scientific_response_selection_v0.py":
        "976ecae7f25c54fdb2e826be5a409a9a9f7840ea81fa5ad507784bdd6c238c4c",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaDeterministicForwardModelPacketReviewScientificResponseSelectionV0.lean":
        "8a32fd9a4ab48ed256348f342b2be6eabeaaebd3395d760e9bb11abecac5b475",
}

FROZEN_V0_SURFACE_KEYS = (
    "comparison_and_geometry",
    "harmonic_contract",
    "production_path",
    "analytic_benchmarks",
    "deliberate_mutations",
    "symmetry_phase_controls",
    "convergence_contract",
    "deterministic_perturbations",
    "canonical_serialization",
    "stage_a_boundary",
    "work_packages",
    "execution_controls",
    "canonical_output_classes",
)

ACCEPTED_GATE_EVIDENCE = {
    "G1_EXACT_PACKET_AUTHORITY_AND_CUSTODY": ["V0_PACKET_CUSTODY_SHA256"],
    "G2_PENDING_REVIEW_STATUS_AND_NO_EXECUTION": ["V0_REVIEW_AND_SCOPE_CUSTODY_SHA256"],
    "G3_STAGE_A_ONLY_SCOPE": ["stage_a_boundary"],
    "G4_FIXED_COMPARISON_AND_APPARATUS_GEOMETRY": ["comparison_and_geometry"],
    "G5_HARMONIC_NORMALIZATION_PHASE_AND_SIGN": ["harmonic_contract"],
    "G6_REAL_150_VECTOR_ORDER_AND_UNITS": ["harmonic_contract"],
    "G7_ONE_SHARED_PRODUCTION_FUNCTION_CHAIN": ["production_path"],
    "G8_UNIFORM_SPHERE_KERNEL_AND_STABLE_FORM_FACTOR": ["production_path"],
    "G9_ANALYTIC_ENERGY_DERIVATIVE_TORQUE": ["production_path"],
    "G10_TWO_GENUINELY_INDEPENDENT_TORQUE_CHECKS": ["production_path"],
    "G11_FOUR_BENCHMARKS_HAVE_EXACT_TARGETS": ["analytic_benchmarks"],
    "G12_FIVE_SCIENTIFIC_MUTATIONS_ROUTE_TO_CONTROLS": ["deliberate_mutations"],
    "G13_SYMMETRY_PHASE_SWAP_AND_ZERO_CONTROLS": ["symmetry_phase_controls"],
    "G14_NEAR_ZERO_ABSOLUTE_FLOOR": ["symmetry_phase_controls", "convergence_contract"],
    "G15_SIXTEEN_PERTURBATION_MAPS_AND_ORDER": ["deterministic_perturbations"],
    "G16_EXPECTED_AMPLITUDE_DEGENERACY_DISCLOSED": [
        "deterministic_perturbations", "retained_jacobian_fields"
    ],
    "G17_JACOBIAN_DIMENSIONS_AND_PARAMETER_ORDER": ["retained_jacobian_fields"],
    "G19_DIMENSIONLESS_SVD_THRESHOLDS": ["retained_jacobian_fields"],
    "G23_CANONICAL_SERIALIZATION_AND_DETERMINISM": ["canonical_serialization"],
    "G24_STAGE_B_EMPIRICAL_AND_THEORY_FIREWALL": ["stage_a_boundary"],
}

REPAIRABLE_GATES = (
    "G18_JACOBIAN_FINITE_DIFFERENCE_STEPS",
    "G20_RANK_DEFICIENT_NUISANCE_PROJECTOR",
    "G21_TRANSITION_DOMAIN_EXACTNESS",
    "G22_IDENTIFIABILITY_REFINEMENT_STABILITY",
)

PARAMETER_ORDER = (
    "LOG_LAMBDA",
    "TORQUE_CALIBRATION",
    "SOURCE_DENSITY_SCALE",
    "DETECTOR_DENSITY_SCALE",
    "DETECTOR_LEVER_OFFSET",
    "ATTRACTOR_LEVER_OFFSET",
    "GAP_OFFSET",
    "ATTRACTOR_AXIS_X_OFFSET",
    "ATTRACTOR_AXIS_Y_OFFSET",
    "ANGULAR_ZERO_OFFSET",
    "HARMONIC_LEAKAGE",
    "BACKGROUND_2RE",
    "BACKGROUND_2IM",
    "BACKGROUND_4RE",
    "BACKGROUND_4IM",
    "BACKGROUND_6RE",
    "BACKGROUND_6IM",
)

FINITE_DIFFERENCE_COLUMNS = (
    "LOG_LAMBDA",
    "DETECTOR_LEVER_OFFSET",
    "ATTRACTOR_LEVER_OFFSET",
    "GAP_OFFSET",
    "ATTRACTOR_AXIS_X_OFFSET",
    "ATTRACTOR_AXIS_Y_OFFSET",
    "ANGULAR_ZERO_OFFSET",
)

EXACT_LINEAR_COLUMNS = tuple(
    parameter for parameter in PARAMETER_ORDER if parameter not in FINITE_DIFFERENCE_COLUMNS
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

TRANSITION_INDICES = tuple(range(4, 21))
TRANSITION_VALUES_M = tuple(10.0 ** (-5.0 + index / 6.0) for index in TRANSITION_INDICES)
REGIME_SENTINEL_VALUES_M = (1e-4 / 3.0, 1e-4, 1e-3, 1e-2, 3e-2)

REVIEW_OUTCOMES = (
    "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY",
    "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
    "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE",
    "BLOCKED_TRANSITION_DOMAIN_CONTRACT",
    "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY",
)

EXECUTION_RESULT_CLASSES = (
    "DETERMINISTIC_FORWARD_MODEL_VALIDATED",
    "BLOCKED_PARAMETER_IDENTIFIABILITY",
    "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED",
    "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
    "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE",
    "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY",
)

PRODUCTION_COMPONENTS = (
    "FROZEN_V0_PRODUCTION_FORWARD_MODEL",
    "V1_JACOBIAN_BUILDER",
    "V1_DIMENSIONLESS_SCALER",
    "V1_THIN_SVD_PROJECTOR",
    "V1_REFINEMENT_ADJUDICATOR",
)

CONTROL_ROWS = (
    (
        "OVERSIZED_DERIVATIVE_STEP",
        "replace_ladder_with_[1.0,0.6,0.3]_at_frozen_mid_domain_fixture",
        "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
    ),
    (
        "UNDERSIZED_NOISE_DOMINATED_STEP",
        "replace_ladder_with_[1e-7,3e-8,1e-8]_and_add_sign_keyed_1e-11_times_Y_star_output_mutation",
        "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
    ),
    (
        "EXACT_DUPLICATE_NUISANCE_COLUMN",
        "replace_one_post_builder_nuisance_column_with_exact_copy_of_another",
        "RANK_REDUCED_WITHOUT_CRASH",
    ),
    (
        "NEAR_DUPLICATE_NUISANCE_COLUMN",
        "replace_one_post_builder_column_by_unit_normalized_1_minus_1e-6_duplicate_plus_1e-6_orthogonal_mixture",
        "NEAR_DEGENERACY_REPORTED",
    ),
    (
        "SVD_THRESHOLD_STABILITY",
        "adjudicate_same_production_jacobian_at_[1e-9,1e-10,1e-11]",
        "RANK_AND_CLASSIFICATION_IDENTICAL_ETA_SPREAD_LE_0.02",
    ),
    (
        "SCALAR_EQUALS_CALIBRATION",
        "replace_actual_scalar_column_with_actual_torque_calibration_column_after_builder",
        "ABS_ETA_LAMBDA_LE_1E-12",
    ),
    (
        "SCALAR_ORTHOGONAL_TO_NUISANCES",
        "inject_lexicographically_first_normalized_coordinate_basis_residual_orthogonal_to_actual_U_r",
        "ABS_ETA_LAMBDA_MINUS_1_LE_1E-12",
    ),
    (
        "POST_RESULT_TRANSITION_POINT_TAMPER",
        "attempt_to_replace_registered_transition_indices_after_production_metrics_exist",
        "BLOCKED_TRANSITION_DOMAIN_CONTRACT",
    ),
    (
        "FORWARD_CONVERGED_JACOBIAN_UNSTABLE",
        "retain_forward_vectors_and_rotate_one_fine_nuisance_column_by_2_degrees",
        "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY",
    ),
    (
        "PRODUCTION_COMPONENT_PROVENANCE",
        "verify_component_identity_and_sha256_at_each_control_boundary",
        "ANY_TEST_SUBSTITUTE_FAILS_PROVENANCE",
    ),
)

REVIEW_BURDEN = (
    "TWENTY_FROZEN_GATES_BYTE_IDENTICAL_OR_SEMANTICALLY_UNCHANGED",
    "FOUR_REPAIRS_EXECUTABLE_NOT_DESCRIPTIVE",
    "ALL_THRESHOLDS_PRECEDE_SCIENTIFIC_OUTPUTS",
    "DIMENSIONLESS_SCALING_PREVENTS_UNIT_CONTROL_OF_SINGULAR_VALUES",
    "RANK_DEFICIENT_CASES_FAIL_SAFELY",
    "NEAR_THRESHOLD_FINDINGS_REMAIN_UNRESOLVED",
    "TEN_CONTROLS_TRAVERSE_PRODUCTION_IMPLEMENTATION",
    "PREPARATION_CALCULATED_NO_FORWARD_VECTOR_JACOBIAN_OR_RESULT",
    "SUCCESS_AUTHORIZES_EXACTLY_ONE_DETERMINISTIC_STAGE_A_EXECUTION",
    "NEW_FOUNDATIONAL_BLOCK_CANNOT_AUTOMATICALLY_CREATE_V2",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, separators=(",", ":"), sort_keys=True).encode("utf-8")


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _assert_selector_authority() -> dict[str, Any]:
    for relative_path, expected_hash in SELECTOR_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"v1 selector authority drift: {relative_path}")
    selector = _load_json(SELECTOR_RELATIVE_PATH)
    if selector.get("selected_route") != "REPAIR_DETERMINISTIC_IDENTIFIABILITY_EXECUTION_CONTRACT":
        raise ValueError("selector route mismatch")
    if selector.get("selected_next_target") != TARGET:
        raise ValueError("selector did not authorize v1 packet preparation")
    if selector.get("scope", {}).get("deterministic_execution_authorized") is not False:
        raise ValueError("selector unexpectedly authorized execution")
    if selector.get("accepted_gate_freeze", {}).get("accepted_gate_count") != 20:
        raise ValueError("selector accepted-gate count mismatch")
    if selector.get("accepted_gate_freeze", {}).get("repairable_gates") != list(REPAIRABLE_GATES):
        raise ValueError("selector repairable-gate mismatch")
    if selector.get("accepted_gate_freeze", {}).get("accepted_gates") != list(
        ACCEPTED_GATE_EVIDENCE
    ):
        raise ValueError("selector accepted-gate identity mismatch")
    return selector


def _assert_v0_custody() -> tuple[dict[str, Any], dict[str, Any], list[dict[str, str]]]:
    review = _load_json(V0_REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_PARAMETER_IDENTIFIABILITY":
        raise ValueError("v0 packet review verdict mismatch")
    if review.get("review_gates", {}).get("pass_count") != 20:
        raise ValueError("v0 accepted-gate count mismatch")
    if review.get("review_gates", {}).get("failure_count") != 4:
        raise ValueError("v0 failed-gate count mismatch")
    custody = review.get("authority", {}).get("frozen_packet_artifacts")
    if not isinstance(custody, list):
        raise ValueError("v0 packet custody list missing")
    for row in custody:
        if _sha256(REPO_ROOT / row["relative_path"]) != row["sha256"]:
            raise ValueError(f"v0 packet custody drift: {row['relative_path']}")
    v0 = _load_json(V0_PACKET_RELATIVE_PATH)
    if v0.get("scope", {}).get("deterministic_execution_performed") is not False:
        raise ValueError("v0 unexpectedly executed")
    return v0, review, custody


def build_packet() -> dict[str, Any]:
    selector = _assert_selector_authority()
    v0, review, v0_custody = _assert_v0_custody()

    frozen_surfaces = {key: deepcopy(v0[key]) for key in FROZEN_V0_SURFACE_KEYS}
    frozen_surface_rows = [
        {
            "surface_id": key,
            "canonical_sha256": _canonical_sha256(frozen_surfaces[key]),
            "semantic_status": "FROZEN_FROM_V0_WITHOUT_CHANGE",
        }
        for key in FROZEN_V0_SURFACE_KEYS
    ]

    v0_jacobian = v0["jacobian_identifiability_contract"]
    retained_jacobian_fields = {
        key: deepcopy(v0_jacobian[key])
        for key in (
            "row_count",
            "column_count",
            "parameter_order",
            "column_standardization",
            "global_output_scale",
            "rank_relative_singular_value_threshold",
            "near_degenerate_absolute_correlation_threshold",
            "exact_projection_residual_threshold",
            "identifiable_eta_threshold",
            "indistinguishable_eta_threshold",
            "minimum_contiguous_identifiable_lambda_points",
            "expected_exact_amplitude_degeneracy",
            "failure_outcome",
        )
    }
    if retained_jacobian_fields["parameter_order"] != list(PARAMETER_ORDER):
        raise ValueError("v0 Jacobian parameter order drift")

    transition_registration = {
        "lambda_grid_formula": "lambda_i=10^(-5+i/6)_m_for_i=0..24",
        "d_min_m": 1e-4,
        "d_max_m": 1e-2,
        "decision_predicate": "d_min/3<=lambda_i<=3*d_max",
        "decision_indices_zero_based": list(TRANSITION_INDICES),
        "decision_values_m": list(TRANSITION_VALUES_M),
        "sentinel_formula": [
            "d_min/3", "d_min", "sqrt(d_min*d_max)", "d_max", "3*d_max"
        ],
        "sentinel_values_m": list(REGIME_SENTINEL_VALUES_M),
    }
    transition_registration_sha256 = _canonical_sha256(transition_registration)

    parameterization = {
        "lambda_coordinate": "q_lambda=log(lambda/1e-3_m)",
        "lambda_reference_m": 1e-3,
        "nuisance_coordinate": "q_j=(p_j-p_j0)/s_j",
        "nuisance_scales": [
            {"parameter_id": row[0], "scale": row[1], "unit": row[2]}
            for row in NUISANCE_SCALES
        ],
        "nuisance_nominal_q": 0.0,
        "nuisance_valid_q_range": [-1.0, 1.0],
        "scale_source": "POSITIVE_HALF_WIDTH_OF_ACCEPTED_V0_TEST_RANGE",
        "result_dependent_scaling": "FORBIDDEN",
    }

    finite_difference = {
        "finite_difference_columns": list(FINITE_DIFFERENCE_COLUMNS),
        "exact_linear_columns": list(EXACT_LINEAR_COLUMNS),
        "dimensionless_step_ladder": [1e-2, 3e-3, 1e-3],
        "interior_formula": "(f(q+h)-f(q-h))/(2h)",
        "lower_boundary_formula": "(-3f(q)+4f(q+h)-f(q+2h))/(2h)",
        "upper_boundary_formula": "(3f(q)-4f(q-h)+f(q-2h))/(2h)",
        "stencil_selection": (
            "CENTERED_IF_VALID_ELSE_SECOND_ORDER_ONE_SIDED_IF_ALL_THREE_POINTS_"
            "VALID_ELSE_BLOCK"
        ),
        "required_evaluation_shape": [150],
        "required_evaluation_order": "GAP_MAJOR_2RE_2IM_4RE_4IM_6RE_6IM",
        "required_evaluation_values": "FINITE_REAL",
        "plateau_steps": [3e-3, 1e-3],
        "plateau_norm": "RMS_AFTER_ACCEPTED_V0_GLOBAL_OUTPUT_SCALING",
        "plateau_absolute_tolerance": 1e-10,
        "plateau_relative_tolerance": 5e-3,
        "plateau_acceptance": "RMS(D_3e-3-D_1e-3)<=1e-10+5e-3*RMS(D_1e-3)",
        "failed_evaluation_outcome": "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
        "failed_plateau_outcome": "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
        "adaptive_step_selection": "FORBIDDEN",
        "fallback_step": "NONE",
        "extrapolation": "NONE",
    }

    projector = {
        "input": "DIMENSIONLESS_PARAMETER_DERIVATIVES_DIVIDED_BY_ACCEPTED_V0_Y_STAR",
        "zero_column_norm_threshold": "sqrt(150)*1e-12",
        "zero_nuisance_column_behavior": "REPORT_AND_EXCLUDE_FROM_UNIT_NORMALIZATION",
        "all_nuisance_columns_zero_behavior": (
            "USE_EMPTY_U_R_RANK_0_ZERO_PSEUDOINVERSE_AND_P_PERP_IDENTITY"
        ),
        "nonzero_nuisance_column_scaling": "UNIT_EUCLIDEAN_NORM",
        "factorization": "THIN_SVD_N_TILDE=U_SIGMA_VT",
        "normal_equation_projector": "FORBIDDEN",
        "central_relative_rank_threshold": 1e-10,
        "probe_relative_rank_thresholds": [1e-9, 1e-11],
        "retained_index_rule": "sigma_i/sigma_1>threshold",
        "pseudoinverse": "V_r*diag(1/sigma_i)*U_r^T",
        "projector": "P_perp=I-U_r*U_r^T",
        "orthonormality_residual": "norm2(U_r^T*U_r-I)",
        "orthonormality_tolerance": 1e-12,
        "reconstruction_residual": (
            "normF(N_tilde-U_r*U_r^T*N_tilde)/max(normF(N_tilde),1e-30)"
        ),
        "reconstruction_tolerance": 1e-9,
        "scalar_zero_norm_behavior": "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED",
        "eta_lambda": "norm2(P_perp*j_lambda)/norm2(j_lambda)",
        "exact_duplicate_behavior": "REDUCE_RANK_WITHOUT_EXCEPTION",
        "near_degeneracy_triggers": [
            "ANY_PAIRWISE_ABSOLUTE_CORRELATION_GE_0.999",
            "RETAINED_CONDITION_NUMBER_GE_1E8",
            "THRESHOLD_PROBE_RANK_DISAGREEMENT",
        ],
        "indistinguishable_point_rule": "eta_lambda<=1e-6",
        "identifiable_point_rule": "eta_lambda>=1e-3",
        "intermediate_point_rule": "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED",
        "rank_or_projector_failure_outcome": "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE",
    }

    transition_domain = {
        "registration": transition_registration,
        "registration_canonical_sha256": transition_registration_sha256,
        "registration_time": "PACKET_PREPARATION_BEFORE_SCIENTIFIC_OUTPUT",
        "required_metrics_at_all_decision_and_sentinel_points": [
            "RETAINED_RANK",
            "SINGULAR_VALUE_SPECTRUM",
            "MAXIMUM_SCALAR_NUISANCE_ABSOLUTE_CORRELATION",
            "NUISANCE_PROJECTOR",
            "ETA_LAMBDA",
            "EXACT_AND_NEAR_DEGENERACY",
            "REFINEMENT_STABILITY",
        ],
        "sentinel_role": "MANDATORY_REGIME_DIAGNOSTIC_NOT_CONTIGUITY_SUBSTITUTE",
        "post_result_selection_or_reordering": "BLOCKED_TRANSITION_DOMAIN_CONTRACT",
        "domain_classification_prerequisite": "ALL_NUMERICAL_STABILITY_RULES_PASS",
        "identifiable_domain_rule": (
            "AT_LEAST_5_CONTIGUOUS_DECISION_POINTS_WITH_ETA_LAMBDA_GE_1E-3"
        ),
        "identifiable_domain_outcome": "DETERMINISTIC_PARAMETER_IDENTIFIABLE",
        "unidentifiable_domain_rule": "ALL_17_DECISION_POINTS_WITH_ETA_LAMBDA_LE_1E-6",
        "unidentifiable_domain_outcome": "BLOCKED_PARAMETER_IDENTIFIABILITY",
        "otherwise": "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED",
    }

    refinement = {
        "levels": [
            {
                "refinement_id": "IDENT_R_MEDIUM",
                "angular_samples": 256,
                "density_cubature_order": 16,
                "energy_derivative_check_step_rad": 2.5e-4,
            },
            {
                "refinement_id": "IDENT_R_FINE",
                "angular_samples": 512,
                "density_cubature_order": 24,
                "energy_derivative_check_step_rad": 1.25e-4,
            },
        ],
        "production_torque": "UNCHANGED_ANALYTIC_NEGATIVE_ENERGY_DERIVATIVE",
        "energy_step_role": "INDEPENDENT_ACCEPTED_CROSS_CHECK_ONLY",
        "retained_rank": "IDENTICAL",
        "eta_absolute_change_max": 0.02,
        "eta_relative_change_max": 0.05,
        "eta_relative_change_condition": "max(abs(eta_medium),abs(eta_fine))>1e-6",
        "maximum_scalar_nuisance_correlation_absolute_change_max": 0.02,
        "largest_principal_angle_definition": (
            "acos(sigma_min(U_medium^T*U_fine))_after_equal_rank_check"
        ),
        "largest_principal_angle_degrees_max": 1.0,
        "decision_bearing_log10_singular_value_change_decades_max": 0.05,
        "decision_bearing_singular_values": "RETAINED_AT_CENTRAL_THRESHOLD_IN_BOTH_LEVELS",
        "exact_and_near_degeneracy_labels": "IDENTICAL",
        "point_classification": "IDENTICAL",
        "threshold_probe_rank": "IDENTICAL",
        "threshold_probe_classification": "IDENTICAL",
        "threshold_probe_eta_spread_max": 0.02,
        "forward_vector_convergence_override": "FORBIDDEN",
        "projector_failure_outcome": "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE",
        "other_failure_outcome": "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY",
    }

    control_rows = [
        {
            "control_id": row[0],
            "mutation_or_probe": row[1],
            "required_outcome": row[2],
            "production_components": list(PRODUCTION_COMPONENTS),
            "test_double_policy": "FORBIDDEN_FOR_PRODUCTION_COMPONENTS",
            "status": "NOT_EXECUTED",
        }
        for row in CONTROL_ROWS
    ]

    preparation_gates = (
        "EXACT_SELECTOR_AUTHORITY_AND_TARGET",
        "V0_PACKET_AND_REVIEW_CUSTODY_VERIFIED",
        "TWENTY_ACCEPTED_GATES_FROZEN",
        "ONLY_G18_G20_G21_G22_REPAIRABLE",
        "THIRTEEN_ACCEPTED_SURFACES_EMBEDDED_UNCHANGED",
        "V0_JACOBIAN_ORDER_SCALE_AND_DECISION_BANDS_RETAINED",
        "DIMENSIONLESS_PARAMETERIZATION_NUMERIC",
        "SEVEN_FINITE_DIFFERENCE_COLUMNS_EXACT",
        "TEN_EXACT_LINEAR_COLUMNS_EXACT",
        "FINITE_DIFFERENCE_STENCILS_AND_LADDER_NUMERIC",
        "PLATEAU_AND_FAILURE_RULES_NUMERIC",
        "THIN_SVD_PSEUDOINVERSE_AND_PROJECTOR_NUMERIC",
        "ZERO_EXACT_NEAR_AND_THRESHOLD_RULES_NUMERIC",
        "ETA_DEFINITION_AND_POINT_BANDS_NUMERIC",
        "SEVENTEEN_TRANSITION_INDICES_REGISTERED",
        "FIVE_REGIME_SENTINELS_REGISTERED",
        "NO_POST_RESULT_POINT_SELECTION",
        "TWO_REFINEMENT_LEVELS_EXACT",
        "SIX_REFINEMENT_STABILITY_CLASSES_NUMERIC",
        "TEN_PRODUCTION_PATH_CONTROLS_FROZEN",
        "TEN_ITEM_INDEPENDENT_REVIEW_BURDEN_FROZEN",
        "FIVE_REVIEW_OUTCOMES_FROZEN",
        "READY_AUTHORIZES_EXACTLY_ONE_EXECUTION",
        "AUTOMATIC_V2_FORBIDDEN",
        "NO_FORWARD_MODEL_VECTOR_JACOBIAN_OR_RESULT_CALCULATED",
        "STAGE_B_EMPIRICAL_AND_THEORY_FIREWALL_RETAINED",
    )

    scope = {
        "packet_preparation_executed": True,
        "v0_frozen_surfaces_embedded": True,
        "finite_difference_contract_frozen": True,
        "rank_deficient_projector_contract_frozen": True,
        "transition_domain_contract_frozen": True,
        "identifiability_refinement_contract_frozen": True,
        "ten_production_control_contract_frozen": True,
        "final_attempt_boundary_frozen": True,
        "independent_packet_review_executed": False,
        "deterministic_execution_authorized": False,
        "deterministic_execution_performed": False,
        "forward_model_called_during_preparation": False,
        "benchmark_executed": False,
        "mutation_executed": False,
        "deterministic_vector_produced": False,
        "jacobian_computed": False,
        "singular_values_computed": False,
        "eta_lambda_computed": False,
        "physical_identifiability_evaluated": False,
        "physical_unidentifiability_established": False,
        "stochastic_packet_preparation_authorized": False,
        "gaussian_noise_used": False,
        "covariance_used": False,
        "monte_carlo_executed": False,
        "profile_likelihood_executed": False,
        "sensitivity_forecast_produced": False,
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
        "schema_id": "toe.scalar_only_yukawa.deterministic_torsion_balance_forward_model_validation.packet.v1",
        "packet_id": "SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_PACKET_20260719_v1",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_selector_verdict": selector["verdict"],
            "consumed_selector_route": selector["selected_route"],
            "frozen_selector_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in SELECTOR_HASHES.items()
            ],
            "frozen_v0_packet_artifacts": deepcopy(v0_custody),
            "consumed_v0_review_verdict": review["verdict"],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_deterministic_torsion_"
                "balance_forward_model_validation_packet_v1.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "repair_authority": {
            "accepted_v0_gate_count": 20,
            "accepted_v0_gates": list(ACCEPTED_GATE_EVIDENCE),
            "accepted_gate_evidence": [
                {"gate_id": gate, "frozen_evidence": evidence}
                for gate, evidence in ACCEPTED_GATE_EVIDENCE.items()
            ],
            "repairable_gate_count": 4,
            "repairable_gates": list(REPAIRABLE_GATES),
            "all_other_gates": "FROZEN_NO_SEMANTIC_CHANGE",
            "automatic_v2": "NOT_AUTHORIZED",
        },
        "frozen_v0_contract": {
            "surface_count": len(FROZEN_V0_SURFACE_KEYS),
            "surface_rows": frozen_surface_rows,
            "surfaces": frozen_surfaces,
            "retained_jacobian_fields": retained_jacobian_fields,
            "retained_jacobian_fields_canonical_sha256": _canonical_sha256(
                retained_jacobian_fields
            ),
        },
        "identifiability_repair_contract": {
            "parameterization": parameterization,
            "g18_finite_difference": finite_difference,
            "g20_rank_deficient_projector": projector,
            "g21_transition_domain": transition_domain,
            "g22_refinement_stability": refinement,
        },
        "production_path_controls": {
            "control_count": len(control_rows),
            "production_component_count": len(PRODUCTION_COMPONENTS),
            "production_components": list(PRODUCTION_COMPONENTS),
            "test_doubles_for_production_components": "FORBIDDEN",
            "declared_mutation_boundary": "INPUTS_OR_RETURNED_ARRAYS_ONLY",
            "rows": control_rows,
        },
        "independent_review_contract": {
            "review_burden_count": len(REVIEW_BURDEN),
            "review_burden": list(REVIEW_BURDEN),
            "outcome_count": len(REVIEW_OUTCOMES),
            "outcomes": list(REVIEW_OUTCOMES),
            "ready_outcome": "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY",
            "ready_authority": READY_EXECUTION_TARGET,
            "ready_execution_limit": 1,
            "blocked_outcome_authority": BLOCKED_REVIEW_RESPONSE_TARGET,
            "blocked_outcome_automatic_v2": "FORBIDDEN",
            "review_itself_may_execute": False,
        },
        "future_single_execution_contract": {
            "status": "NOT_AUTHORIZED_PENDING_INDEPENDENT_REVIEW",
            "maximum_execution_count_after_ready_review": 1,
            "result_classes": list(EXECUTION_RESULT_CLASSES),
            "scientific_question": (
                "DOES_SCALAR_RANGE_CHANGE_REAL_150_SHAPE_OUTSIDE_SPAN_OF_"
                "SIXTEEN_DETERMINISTIC_APPARATUS_PERTURBATIONS"
            ),
            "stage_b": "NOT_AUTHORIZED",
            "noise": "NONE",
            "monte_carlo": "NONE",
            "likelihood": "NONE",
            "forecast": "NONE",
            "constraint": "NONE",
        },
        "preparation_gates": {
            "gate_count": len(preparation_gates),
            "pass_count": len(preparation_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in preparation_gates],
        },
        "scope": scope,
        "current_posture": {
            "v0_packet_review": "BLOCKED_PARAMETER_IDENTIFIABILITY_CONTRACT_INCOMPLETE",
            "v0_accepted_gates": "20_OF_24_FROZEN",
            "v1_packet": "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "v1_editable_gates": "G18_G20_G21_G22_ONLY",
            "deterministic_execution": "NOT_AUTHORIZED_NOT_PERFORMED",
            "forward_vector": "NOT_PRODUCED",
            "jacobian": "NOT_COMPUTED",
            "physical_identifiability": "NOT_EVALUATED",
            "stage_b": "DEFERRED_NOT_AUTHORIZED",
            "synthetic_forecast": "NONE",
            "empirical_evidence": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "automatic_v2": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This artifact prepares the final four-interface deterministic "
            "identifiability contract repair and rotates only to independent packet "
            "review. It preserves the twenty accepted v0 gates and calculates no "
            "forward vector, Jacobian, singular value, correlation, projector, eta, "
            "identifiability result, bound, forecast, empirical claim, parameter "
            "choice, scalar-branch adoption, native bridge, principle, or action."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_packet(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the final deterministic Yukawa identifiability repair packet v1."
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
            print("deterministic identifiability repair packet v1 already current")
        return 0
    if current != expected:
        print("deterministic identifiability repair packet v1 drift")
        return 1
    print("deterministic identifiability repair packet v1 OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
