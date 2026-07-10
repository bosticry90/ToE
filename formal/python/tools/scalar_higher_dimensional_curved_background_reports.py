from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"
REVISED_AT_UTC = "2026-07-10T00:00:00Z"

GUARDRAIL_TARGET = (
    "prepare_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_guardrail_packet"
)
GUARDRAIL_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_higher_dimensional_"
    "curved_background_guardrail_packet"
)
EXECUTION_TARGET = (
    "execute_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_v0"
)
EXECUTION_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_higher_dimensional_"
    "curved_background_calculation_execution"
)
REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_v0_result"
)
REVIEW_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_higher_dimensional_"
    "curved_background_calculation_result_review"
)
DIAGNOSTIC_FAILURE_TARGET = (
    "diagnose_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_v0_threshold_failure"
)

GUARDRAIL_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_GUARDRAIL_PACKET_PREPARED_AUTHORIZES_FIXED_2PLUS1_"
    "SPATIALLY_VARYING_WARPED_GEOMETRY_MATTER_IDENTITY_CALCULATION_ONLY"
)
GUARDRAIL_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_GUARDRAIL_PACKET_PREPARED_LEVEL_3_FIXED_BACKGROUND_"
    "SCOPED_E_REPRO_SPRINT_ONLY_NO_GRAVITY_EVOLUTION_NO_EINSTEIN_SOURCE_"
    "NO_BIANCHI_COMPATIBILITY_NO_QFT_GR_SEAM_ADMISSIBILITY_OR_PROMOTION"
)
EXECUTION_OUTCOME = (
    "CALC_SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_"
    "DIMENSIONAL_CURVED_BACKGROUND_EXECUTED_FIXED_2PLUS1_WARPED_GEOMETRY_"
    "MATTER_IDENTITY_TESTED_NO_EINSTEIN_SOURCE_OR_SEAM_ADMISSIBILITY_CLAIM"
)
EXECUTION_STRICT_OUTCOME = (
    "CALC_SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_"
    "DIMENSIONAL_CURVED_BACKGROUND_EXECUTED_LEVEL3_CANDIDATE_E_REPRO_"
    "PENDING_REVIEW_NO_BIANCHI_COMPATIBILITY_NO_QFT_GR_SEAM_CLOSURE_NO_"
    "MASTER_ACTION_PROMOTION"
)
EXECUTION_BLOCKED_OUTCOME = (
    "CALC_SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_"
    "DIMENSIONAL_CURVED_BACKGROUND_EXECUTED_BLOCKED_THRESHOLD_FAILURE_"
    "ARTIFACTS_PRESERVED"
)
EXECUTION_BLOCKED_STRICT_OUTCOME = (
    "CALC_SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_"
    "DIMENSIONAL_CURVED_BACKGROUND_BLOCKED_NO_E_REPRO_ACCEPTANCE_NO_"
    "THRESHOLD_RELAXATION_DIAGNOSTIC_TARGET_SELECTED"
)

PACKET_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_GUARDRAIL_PACKET_20260709_v1"
)
PACKET_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_GUARDRAIL_PACKET_v1"
)
SUPERSEDED_PACKET_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_GUARDRAIL_PACKET_20260709_v0"
)
SUPERSEDED_PACKET_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_GUARDRAIL_PACKET_v0"
)
CALCULATION_ID = (
    "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-HIGHER-"
    "DIMENSIONAL-CURVED-BACKGROUND-v0"
)
EQUATION_ID = "EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0"
BACKGROUND_GEOMETRY_CLASSIFICATION = (
    "fixed_nonzero_spatially_varying_curvature_2plus1_warped_periodic_"
    "background"
)

PREDECESSOR_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
    "CURVATURE_BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0.json"
)
EXPECTED_PREDECESSOR_REVIEW_SHA256 = (
    "538ba6db4e42cdcbaf5f109e3e4beb4c79b0e740db134d04d7293ef1a05d5702"
)
READINESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
EXPECTED_READINESS_SHA256 = (
    "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1"
)
SUPERSEDED_GUARDRAIL_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_"
    "DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_PACKET_20260709_v0.json"
)
EXPECTED_SUPERSEDED_GUARDRAIL_SHA256 = (
    "381adc90f542e6cca4dbfe1c2b858d59ee763ed804c9aa07be08feb00118bfe8"
)
GUARDRAIL_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_"
    "DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_PACKET_20260709_v1.json"
)
EXPECTED_GUARDRAIL_SHA256 = (
    "e6ce9dfb08364e3fa3a0a3895a3d1b16635348ab2fc7b0490f0b3b6e04db6b96"
)
CALCULATION_SCRIPT_RELATIVE_PATH = (
    "formal/python/toe/calculations/"
    "calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background.py"
)
CALCULATION_OUTPUT_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "HIGHER-DIMENSIONAL-CURVED-BACKGROUND-v0.json"
)
CALCULATION_MANIFEST_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "HIGHER-DIMENSIONAL-CURVED-BACKGROUND-MANIFEST-v0.json"
)
EXECUTION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "HIGHER_DIMENSIONAL_CURVED_BACKGROUND_CALCULATION_EXECUTION_20260709_v0.json"
)
CALCULATION_SCRIPT_PATH = REPO_ROOT / CALCULATION_SCRIPT_RELATIVE_PATH
CALCULATION_OUTPUT_PATH = REPO_ROOT / CALCULATION_OUTPUT_RELATIVE_PATH
CALCULATION_MANIFEST_PATH = REPO_ROOT / CALCULATION_MANIFEST_RELATIVE_PATH
EXECUTION_REPORT_PATH = REPO_ROOT / EXECUTION_REPORT_RELATIVE_PATH
EXECUTION_REPORT_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_CALCULATION_EXECUTION_20260709_v0"
)
EXECUTION_REPORT_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_"
    "CURVED_BACKGROUND_CALCULATION_EXECUTION_v0"
)
CALCULATION_RESULT_SCHEMA_ID = f"{CALCULATION_ID}-RESULT"
CALCULATION_MANIFEST_SCHEMA_ID = f"{CALCULATION_ID}-MANIFEST"
CALCULATION_EXECUTION_COMMAND = (
    "python -m formal.python.toe.calculations."
    "calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background"
)

SPATIAL_RESOLUTIONS = [32, 64, 128, 256]
TIME_SLICES = [0.0, 0.37, 0.91]
EPSILON_R = 1e-12
EPSILON_NORM = 1e-14
EPSILON_CONTROL = 1e-14
COORDINATE_GRID_NORM_NAME = "coordinate_grid_euclidean_component_rms"
NEGATIVE_CONTROL_IDS = {
    "naive_partial_divergence",
    "omitted_tensor_index_connection_term",
    "omitted_volume_trace_connection_term",
    "curved_case_flat_geometry_substitution",
    "incorrect_y_inverse_metric_factor",
}
THRESHOLD_IDS = {
    "minimum_two_finest_y_mode_convergence_order",
    "minimum_two_finest_x_mode_convergence_order",
    "maximum_finest_y_mode_combined_relative_identity_error",
    "maximum_finest_x_mode_combined_relative_identity_error",
    "maximum_finest_on_shell_combined_absolute_divergence_error",
    "maximum_analytic_profile_residual_reference_error",
    "maximum_metric_compatibility_absolute_error",
    "maximum_curvature_route_absolute_discrepancy",
    "minimum_curvature_peak_absolute_value",
    "minimum_curvature_peak_to_peak_variation",
    "maximum_flat_limit_absolute_discrepancy",
    "minimum_naive_partial_divergence_error_ratio",
    "minimum_omitted_tensor_index_term_error_ratio",
    "minimum_omitted_volume_trace_term_error_ratio",
    "minimum_flat_geometry_substitution_normalized_discrepancy",
    "minimum_incorrect_y_inverse_metric_normalized_discrepancy",
}
FROZEN_SUCCESS_CRITERIA = {
    "minimum_two_finest_y_mode_convergence_order": 1.8,
    "minimum_two_finest_x_mode_convergence_order": 1.8,
    "maximum_finest_y_mode_combined_relative_identity_error": 0.02,
    "maximum_finest_x_mode_combined_relative_identity_error": 0.02,
    "maximum_finest_on_shell_combined_absolute_divergence_error": 1e-11,
    "maximum_analytic_profile_residual_reference_error": 1e-12,
    "maximum_metric_compatibility_absolute_error": 1e-12,
    "maximum_curvature_route_absolute_discrepancy": 1e-12,
    "minimum_curvature_peak_absolute_value": 0.49,
    "minimum_curvature_peak_to_peak_variation": 0.8,
    "maximum_flat_limit_absolute_discrepancy": 1e-11,
    "minimum_naive_partial_divergence_error_ratio": 10.0,
    "minimum_omitted_tensor_index_term_error_ratio": 10.0,
    "minimum_omitted_volume_trace_term_error_ratio": 10.0,
    "minimum_flat_geometry_substitution_normalized_discrepancy": 0.02,
    "minimum_incorrect_y_inverse_metric_normalized_discrepancy": 0.02,
}
FROZEN_THRESHOLD_DECISIONS = [
    {
        "decision_number": 1,
        "threshold_id": "minimum_two_finest_x_mode_convergence_order",
        "comparison": ">=",
        "threshold": 1.8,
        "evidence": "off_shell_x_mode p_min",
    },
    {
        "decision_number": 2,
        "threshold_id": "minimum_two_finest_y_mode_convergence_order",
        "comparison": ">=",
        "threshold": 1.8,
        "evidence": "off_shell_y_mode p_min",
    },
    {
        "decision_number": 3,
        "threshold_id": "maximum_finest_x_mode_combined_relative_identity_error",
        "comparison": "<=",
        "threshold": 0.02,
        "evidence": "N=256 off_shell_x_mode combined relative identity error",
    },
    {
        "decision_number": 4,
        "threshold_id": "maximum_finest_y_mode_combined_relative_identity_error",
        "comparison": "<=",
        "threshold": 0.02,
        "evidence": "N=256 off_shell_y_mode combined relative identity error",
    },
    {
        "decision_number": 5,
        "threshold_id": (
            "maximum_finest_on_shell_combined_absolute_divergence_error"
        ),
        "comparison": "<=",
        "threshold": 1e-11,
        "evidence": "N=256 temporal-mode combined absolute divergence error",
    },
    {
        "decision_number": 6,
        "threshold_id": (
            "maximum_analytic_profile_residual_reference_error"
        ),
        "comparison": "<=",
        "threshold": 1e-12,
        "evidence": (
            "maximum explicit-profile residual versus independently assembled "
            "analytic derivative reference"
        ),
    },
    {
        "decision_number": 7,
        "threshold_id": "maximum_metric_compatibility_absolute_error",
        "comparison": "<=",
        "threshold": 1e-12,
        "evidence": "maximum absolute component of nabla_lambda g_mu_nu",
    },
    {
        "decision_number": 8,
        "threshold_id": "maximum_curvature_route_absolute_discrepancy",
        "comparison": "<=",
        "threshold": 1e-12,
        "evidence": "maximum abs(R_generic-R_analytic) over all frozen grids",
    },
    {
        "decision_number": 9,
        "threshold_id": "minimum_curvature_peak_absolute_value",
        "comparison": ">=",
        "threshold": 0.49,
        "evidence": "maximum abs(R_analytic) over the frozen background",
    },
    {
        "decision_number": 10,
        "threshold_id": "minimum_curvature_peak_to_peak_variation",
        "comparison": ">=",
        "threshold": 0.8,
        "evidence": "max(R_analytic)-min(R_analytic)",
    },
    {
        "decision_number": 11,
        "threshold_id": "maximum_flat_limit_absolute_discrepancy",
        "comparison": "<=",
        "threshold": 1e-11,
        "evidence": "generic epsilon=0 route versus independent Cartesian route",
    },
    {
        "decision_number": 12,
        "threshold_id": "minimum_naive_partial_divergence_error_ratio",
        "comparison": ">=",
        "threshold": 10.0,
        "evidence": "minimum of N=256 x-mode and y-mode control ratios",
    },
    {
        "decision_number": 13,
        "threshold_id": "minimum_omitted_tensor_index_term_error_ratio",
        "comparison": ">=",
        "threshold": 10.0,
        "evidence": "N=256 temporal-mode omitted tensor-index ratio",
    },
    {
        "decision_number": 14,
        "threshold_id": "minimum_omitted_volume_trace_term_error_ratio",
        "comparison": ">=",
        "threshold": 10.0,
        "evidence": "N=256 temporal-mode omitted volume-trace ratio",
    },
    {
        "decision_number": 15,
        "threshold_id": (
            "minimum_flat_geometry_substitution_normalized_discrepancy"
        ),
        "comparison": ">=",
        "threshold": 0.02,
        "evidence": "minimum of N=256 x-mode and y-mode discrepancies",
    },
    {
        "decision_number": 16,
        "threshold_id": (
            "minimum_incorrect_y_inverse_metric_normalized_discrepancy"
        ),
        "comparison": ">=",
        "threshold": 0.02,
        "evidence": "N=256 y-mode wrong-inverse-metric discrepancy",
    },
]


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def report_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _verified_predecessor_hash() -> str:
    actual = sha256_path(PREDECESSOR_REVIEW_PATH)
    if actual != EXPECTED_PREDECESSOR_REVIEW_SHA256:
        raise ValueError("accepted predecessor review hash differs")
    return actual


def _verified_readiness_hash() -> str:
    actual = sha256_path(READINESS_PATH)
    if actual != EXPECTED_READINESS_SHA256:
        raise ValueError("science-readiness authority hash differs")
    return actual


def _verified_superseded_guardrail_hash() -> str:
    actual = sha256_path(SUPERSEDED_GUARDRAIL_REPORT_PATH)
    if actual != EXPECTED_SUPERSEDED_GUARDRAIL_SHA256:
        raise ValueError("superseded v0 guardrail bytes differ")
    return actual


def build_guardrail_payload() -> dict[str, Any]:
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "prepared_authorizes_execution_only",
        "captured_at_utc": CAPTURED_AT_UTC,
        "revised_at_utc": REVISED_AT_UTC,
        "supersession": {
            "supersedes_schema_id": SUPERSEDED_PACKET_SCHEMA_ID,
            "supersedes_packet_id": SUPERSEDED_PACKET_ID,
            "supersedes_path": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_"
                "DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_CURVED_BACKGROUND_"
                "GUARDRAIL_PACKET_20260709_v0.json"
            ),
            "supersedes_sha256": _verified_superseded_guardrail_hash(),
            "original_captured_at_utc": CAPTURED_AT_UTC,
            "revision_reason": (
                "freeze non-gating curvature-zero relative-error reporting, "
                "complete analytic residual and norm contracts, exact negative "
                "control defects, and the sixteen threshold decisions"
            ),
            "superseded_artifact_preserved_byte_for_byte": True,
        },
        "consumed_target": GUARDRAIL_TARGET,
        "consumed_target_kind": GUARDRAIL_TARGET_KIND,
        "selected_next_target": EXECUTION_TARGET,
        "selected_next_target_kind": EXECUTION_TARGET_KIND,
        "packet_result": GUARDRAIL_OUTCOME,
        "strict_packet_result": GUARDRAIL_STRICT_OUTCOME,
        "calculation_id": CALCULATION_ID,
        "accepted_predecessor": {
            "artifact_id": (
                "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
                "NONZERO_CURVATURE_BACKGROUND_CALCULATION_RESULT_REVIEW_v0"
            ),
            "path": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_"
                "DIVERGENCE_IDENTITY_NONZERO_CURVATURE_BACKGROUND_"
                "CALCULATION_RESULT_REVIEW_20260709_v0.json"
            ),
            "sha256": _verified_predecessor_hash(),
            "accepted_claim_ceiling": "Level 3 scoped E-REPRO",
            "accepted_scope": (
                "one fixed genuinely curved 1+1 de Sitter matter identity only"
            ),
        },
        "readiness_authority": {
            "artifact_id": "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0",
            "path": "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json",
            "sha256": _verified_readiness_hash(),
            "status": "accepted_current_science_sprint_readiness_authority",
        },
        "question": (
            "Does the scalar covariant stress-energy divergence identity hold "
            "numerically for three independent divergence components and "
            "multiple field profiles on one fixed 2+1-dimensional periodic "
            "warped background with spatially varying curvature?"
        ),
        "inputs": {
            "coordinates": ["t", "x", "y"],
            "coordinate_indices": {"t": 0, "x": 1, "y": 2},
            "spacetime_dimension": 3,
            "dimension_label": "2+1",
            "coordinate_domain": {
                "t": "frozen evaluation slices in [0,1]",
                "x": "x in [0,2*pi), periodic",
                "y": "y in [0,2*pi), periodic",
            },
            "time_slices": list(TIME_SLICES),
            "spatial_resolutions_Nx_equals_Ny": list(SPATIAL_RESOLUTIONS),
            "resolution_symbol_N_means": "N x N spatial grid",
            "periodic_endpoint_duplicated": False,
            "warp_amplitude_epsilon": 0.2,
            "warp_factor": "f(x) = 1 + epsilon*cos(x)",
            "warp_factor_derivatives": {
                "f_prime": "f'(x) = -epsilon*sin(x)",
                "f_double_prime": "f''(x) = -epsilon*cos(x)",
            },
            "warp_factor_minimum": 0.8,
            "warp_factor_maximum": 1.2,
            "maximum_inverse_y_metric_factor": 1.5625,
            "minimum_absolute_metric_determinant": 0.64,
            "amplitude_A": 0.2,
            "mass_m": 1.0,
        },
        "background_geometry": {
            "classification": BACKGROUND_GEOMETRY_CLASSIFICATION,
            "fixed_background_only": True,
            "metric_signature": "(-,+,+)",
            "metric": "g_mu_nu = diag(-1, 1, f(x)^2)",
            "inverse_metric": "g^mu_nu = diag(-1, 1, f(x)^(-2))",
            "determinant": "det(g_mu_nu) = -f(x)^2",
            "volume_density": "sqrt(-g) = f(x), because f(x) >= 0.8",
            "nonsingularity_witness": "min_x f(x) = 1-epsilon = 0.8 > 0",
            "scalar_curvature": (
                "R(x) = -2*f''(x)/f(x) = "
                "2*epsilon*cos(x)/(1+epsilon*cos(x))"
            ),
            "scalar_curvature_minimum": -0.5,
            "scalar_curvature_maximum": 0.3333333333333333,
            "scalar_curvature_peak_to_peak": 0.8333333333333333,
            "curvature_spatially_varying": True,
            "curvature_zero_crossings_allowed": True,
            "curvature_zero_crossings_exact": ["pi/2", "3*pi/2"],
            "gravity_evolved": False,
        },
        "connection_and_curvature_conventions": {
            "christoffel_definition": (
                "Gamma^rho_{mu nu} = 1/2 g^{rho sigma} "
                "(partial_mu g_{sigma nu} + partial_nu g_{sigma mu} - "
                "partial_sigma g_{mu nu})"
            ),
            "nonzero_christoffels": {
                "Gamma^x_{y y}": "-f(x)*f'(x)",
                "Gamma^y_{x y}": "f'(x)/f(x)",
                "Gamma^y_{y x}": "f'(x)/f(x)",
            },
            "all_time_index_christoffels_zero": True,
            "riemann_sign": (
                "R^rho_{sigma mu nu} = partial_mu Gamma^rho_{nu sigma} - "
                "partial_nu Gamma^rho_{mu sigma} + "
                "Gamma^rho_{mu lambda} Gamma^lambda_{nu sigma} - "
                "Gamma^rho_{nu lambda} Gamma^lambda_{mu sigma}"
            ),
            "ricci_contraction": "R_{sigma nu} = R^rho_{sigma rho nu}",
            "scalar_contraction": "R = g^{sigma nu} R_{sigma nu}",
            "expected_ricci_components": {
                "R_t t": "0",
                "R_x x": "-f''(x)/f(x)",
                "R_y y": "-f(x)*f''(x)",
            },
            "expected_einstein_components": {
                "G_t t": "R(x)/2 = -f''(x)/f(x)",
                "G_x x": "0",
                "G_y y": "0",
            },
            "einstein_tensor_not_identically_zero": True,
            "einstein_tensor_source_tested": False,
        },
        "curvature_verification": {
            "analytic_warped_product_route": {
                "formula": "R_analytic(x) = -2*f''(x)/f(x)",
                "substituted_formula": (
                    "R_analytic(x) = 0.4*cos(x)/(1+0.2*cos(x))"
                ),
                "expected_range": [-0.5, 0.3333333333333333],
            },
            "independent_generic_tensor_route": {
                "route": [
                    "metric",
                    "inverse_metric",
                    "metric_derivatives",
                    "Christoffel_symbols",
                    "Riemann_tensor",
                    "Ricci_tensor",
                    "scalar_contraction",
                ],
                "implementation_independence": (
                    "generic index-loop symbolic reconstruction; do not call "
                    "or substitute the analytic warped-product curvature formula"
                ),
                "comparison_scope": "all frozen x grid points at every resolution",
            },
            "maximum_route_agreement_absolute_error": 1e-12,
            "minimum_peak_absolute_scalar_curvature": 0.49,
            "minimum_peak_to_peak_scalar_curvature": 0.8,
            "metric_compatibility_required": True,
            "curvature_zero_exclusion_policy": {
                "epsilon_R": EPSILON_R,
                "absolute_error_formula": "abs(R_generic-R_analytic)",
                "absolute_error_reported_at_every_x_index": True,
                "relative_error_formula_away_from_zero": (
                    "abs(R_generic-R_analytic)/abs(R_analytic)"
                ),
                "exclusion_condition": "abs(R_analytic) <= epsilon_R",
                "excluded_relative_error_value": None,
                "excluded_status": "excluded_near_zero",
                "non_gating_reporting_rule": True,
                "not_an_additional_success_threshold": True,
                "exact_crossing_locations": ["pi/2", "3*pi/2"],
                "per_resolution_exclusions": [
                    {
                        "resolution_N": resolution,
                        "excluded_x_index_count": 2,
                        "excluded_x_indices": [resolution // 4, 3 * resolution // 4],
                        "excluded_spatial_gridpoint_count": 2 * resolution,
                    }
                    for resolution in SPATIAL_RESOLUTIONS
                ],
            },
        },
        "equation_surfaces": {
            "scalar_action": (
                "S[phi,g] = integral d^3x sqrt(-g) [-1/2 g^{mu nu} "
                "partial_mu phi partial_nu phi - 1/2 m^2 phi^2]"
            ),
            "potential": "V(phi) = 1/2 m^2 phi^2",
            "potential_derivative": "V'(phi) = m^2 phi",
            "stress_energy": (
                "T^{mu nu} = nabla^mu phi nabla^nu phi - g^{mu nu} "
                "[1/2 nabla_alpha phi nabla^alpha phi + 1/2 m^2 phi^2]"
            ),
            "field_residual": "E_phi = Box_g phi - m^2 phi",
            "covariant_dalembertian": (
                "Box_g phi = -partial_t^2 phi + partial_x^2 phi + "
                "[f'(x)/f(x)] partial_x phi + "
                "f(x)^(-2) partial_y^2 phi"
            ),
            "covariant_divergence": (
                "nabla_mu T^{mu nu} = partial_mu T^{mu nu} + "
                "Gamma^mu_{mu lambda} T^{lambda nu} + "
                "Gamma^nu_{mu lambda} T^{mu lambda}"
            ),
            "volume_trace_connection_term": (
                "Gamma^mu_{mu lambda} T^{lambda nu}"
            ),
            "tensor_index_connection_term": (
                "Gamma^nu_{mu lambda} T^{mu lambda}"
            ),
            "identity": "nabla_mu T^{mu nu} = E_phi nabla^nu phi",
            "analytic_profile_residual_reference_assembly": (
                "-phi_tt + phi_xx + [f'(x)/f(x)]*phi_x + "
                "f(x)^(-2)*phi_yy - m^2*phi"
            ),
            "analytic_profile_residual_reference_metric": (
                "maximum_analytic_profile_residual_reference_error"
            ),
            "divergence_components_required": [0, 1, 2],
            "divergence_component_labels": ["nu=t", "nu=x", "nu=y"],
            "existing_equation_id_reused": EQUATION_ID,
            "existing_equation_status": (
                "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"
            ),
            "new_equation_identity_created": False,
            "equation_surface_upgraded": False,
            "equation_compendium_edited": False,
        },
        "solution_controls": {
            "on_shell_temporal_mode": {
                "field": "phi_on(t) = A*cos(m*t)",
                "parameters": {"A": 0.2, "m": 1.0},
                "classification": "exact_source_free_on_shell_solution",
                "forced_or_manufactured": False,
                "exact_residual": "E_phi = 0",
                "role": (
                    "on-shell positive control; spatial stress components still "
                    "enter connection terms in the covariant divergence"
                ),
            },
            "off_shell_y_mode": {
                "field": "phi_y(t,y) = A*cos(omega_y*t)*cos(ell*y)",
                "parameters": {"A": 0.2, "omega_y": 1.5, "ell": 2},
                "classification": "deliberately_off_shell_unforced_field",
                "forced_or_manufactured": False,
                "exact_residual": (
                    "E_phi = [omega_y^2-m^2-ell^2/f(x)^2]*phi_y"
                ),
                "substituted_exact_residual": (
                    "E_phi = [1.25-4/f(x)^2]*phi_y"
                ),
                "purpose": (
                    "exercise the second spatial derivative direction and the "
                    "spatially varying inverse metric"
                ),
            },
            "off_shell_x_mode": {
                "field": "phi_x(t,x) = A*cos(omega_x*t)*cos(k*x)",
                "parameters": {"A": 0.2, "omega_x": 1.7, "k": 2},
                "classification": "deliberately_off_shell_unforced_field",
                "forced_or_manufactured": False,
                "exact_residual": (
                    "E_phi = (omega_x^2-m^2-k^2)*phi_x - "
                    "A*k*[f'(x)/f(x)]*cos(omega_x*t)*sin(k*x)"
                ),
                "purpose": (
                    "exercise x derivatives and the f'(x)/f(x) scalar "
                    "connection term independently of the y derivative route"
                ),
            },
        },
        "numerical_method": {
            "temporal_derivatives": "analytic",
            "metric_connection_and_temporal_field_derivatives": "analytic",
            "spatial_discretization": (
                "second-order centered finite differences on a periodic x-y grid"
            ),
            "periodic_boundary_handling": (
                "index wrapping independently in x and y; endpoints not duplicated"
            ),
            "refinement_schedule": {
                "Nx_equals_Ny": list(SPATIAL_RESOLUTIONS),
                "delta_x_equals_delta_y": "2*pi/N",
                "refinement_ratio": 2,
            },
            "component_rms_norm_at_each_time": (
                "sqrt(mean_{x,y}((identity_error^nu)^2)) for each nu"
            ),
            "combined_rms_norm_at_each_time": (
                "sqrt(mean_{x,y}(sum_{nu=0}^2 (identity_error^nu)^2))"
            ),
            "space_time_component_rms_norm": (
                "sqrt(mean_{t,x,y}((identity_error^nu)^2))"
            ),
            "space_time_combined_rms_norm": (
                "sqrt(mean_{t,x,y}(sum_{nu=0}^2 (identity_error^nu)^2))"
            ),
            "norm_contract": {
                "name": COORDINATE_GRID_NORM_NAME,
                "coordinate_grid_uniform_unweighted": True,
                "coordinate_invariant_tensor_norm": False,
                "curved_volume_weighted": False,
                "epsilon_norm": EPSILON_NORM,
                "epsilon_control": EPSILON_CONTROL,
                "component_rms": "sqrt(mean(error_nu^2))",
                "combined_rms": "sqrt(mean(error_t^2+error_x^2+error_y^2))",
                "off_shell_component_relative_error": (
                    "RMS(divergence_nu-RHS_nu)/"
                    "max(RMS(RHS_nu),epsilon_norm)"
                ),
                "control_error_ratio": (
                    "defective_error/max(correct_error,epsilon_control)"
                ),
                "normalized_defect_discrepancy": (
                    "RMS(defective-correct_curved_RHS)/"
                    "max(RMS(correct_curved_RHS),epsilon_control)"
                ),
            },
            "off_shell_relative_error": (
                "norm(nabla_mu T^{mu nu}-E_phi*nabla^nu phi) / "
                "max(norm(E_phi*nabla^nu phi),epsilon_norm)"
            ),
            "on_shell_error_policy": (
                "report absolute componentwise and combined divergence norms; "
                "do not report a relative error against the zero reference"
            ),
            "convergence_order": "log2(error_N/error_2N)",
            "convergence_profiles": ["off_shell_y_mode", "off_shell_x_mode"],
            "convergence_gate": {
                "error_N": (
                    "combined space-time coordinate-grid identity-error RMS"
                ),
                "p_64_128": "log2(error_64/error_128)",
                "p_128_256": "log2(error_128/error_256)",
                "p_min": "min(p_64_128,p_128_256)",
                "adjudication": (
                    "p_min >= 1.8 separately for off_shell_x_mode and "
                    "off_shell_y_mode"
                ),
                "component_orders_diagnostic_only": True,
            },
            "determinism": (
                "two fresh-process regenerations must match canonical result, "
                "manifest, and execution-report bytes"
            ),
        },
        "flat_limit_control": {
            "positive_control": {
                "substitution": "epsilon -> 0, hence f -> 1",
                "expected_metric": "diag(-1,1,1)",
                "expected_connection": "all Christoffel symbols vanish",
                "expected_scalar_curvature": 0.0,
                "operator_coefficients_exact": [-1, 1, 1],
                "operator_coefficient_order": [
                    "partial_t^2",
                    "partial_x^2",
                    "partial_y^2",
                ],
                "maximum_numeric_discrepancy": 1e-11,
                "independent_floating_route_byte_equality_required": False,
                "comparison": (
                    "correct 2+1 implementation must reproduce the analytic "
                    "Cartesian Minkowski identity for all three profiles"
                ),
            },
            "distinct_from_negative_control": (
                "the positive control changes both geometry and analytic "
                "reference; the negative control substitutes flat geometry into "
                "the epsilon=0.2 curved case while retaining its curved reference"
            ),
        },
        "negative_controls": {
            "naive_partial_divergence": {
                "operation": (
                    "omit both Gamma^mu_{mu lambda} T^{lambda nu} and "
                    "Gamma^nu_{mu lambda} T^{mu lambda} from nabla_mu "
                    "T^{mu nu}; retain the correct stress tensor and curved RHS"
                ),
                "evaluation": (
                    "evaluate the y-mode and x-mode spatial off-shell profiles "
                    "separately; the adjudicated value is the minimum of the "
                    "two profile-specific ratios so neither profile can be masked"
                ),
                "ratio_definition": (
                    "space-time combined RMS defective identity error divided "
                    "by max(space-time combined RMS correct covariant identity "
                    "error,epsilon_control), evaluated separately for each "
                    "required profile"
                ),
                "minimum_error_ratio_to_correct_covariant_result": 10.0,
            },
            "omitted_tensor_index_connection_term": {
                "operation": "omit Gamma^nu_{mu lambda} T^{mu lambda} only",
                "evaluation": (
                    "on-shell temporal mode, where the two connection terms "
                    "must cancel componentwise in the correct calculation"
                ),
                "ratio_definition": (
                    "space-time combined RMS defective on-shell divergence "
                    "divided by max(correct on-shell combined absolute "
                    "divergence error,epsilon_control)"
                ),
                "minimum_error_ratio_to_correct_covariant_result": 10.0,
            },
            "omitted_volume_trace_connection_term": {
                "operation": "omit Gamma^mu_{mu lambda} T^{lambda nu} only",
                "evaluation": (
                    "on-shell temporal mode, where the two connection terms "
                    "must cancel componentwise in the correct calculation"
                ),
                "ratio_definition": (
                    "space-time combined RMS defective on-shell divergence "
                    "divided by max(correct on-shell combined absolute "
                    "divergence error,epsilon_control)"
                ),
                "minimum_error_ratio_to_correct_covariant_result": 10.0,
            },
            "curved_case_flat_geometry_substitution": {
                "operation": (
                    "set epsilon=0 in the defective metric, inverse metric, "
                    "connection, stress tensor, and divergence while retaining "
                    "the epsilon=0.2 correct curved analytic RHS reference"
                ),
                "evaluation": (
                    "evaluate the y-mode and x-mode separately; the adjudicated "
                    "value is the minimum profile-specific normalized discrepancy"
                ),
                "normalized_discrepancy_definition": (
                    "space-time combined RMS(flat-substituted divergence minus "
                    "correct curved analytic RHS) divided by max(space-time "
                    "combined RMS correct curved analytic RHS,epsilon_control)"
                ),
                "minimum_normalized_discrepancy": 0.02,
            },
            "incorrect_y_inverse_metric_factor": {
                "operation": (
                    "in the defective y-mode scalar/RHS route replace "
                    "g^yy=f(x)^(-2) by g^yy=1 everywhere it enters the y "
                    "residual and raised y-gradient"
                ),
                "comparison_reference": (
                    "retain the correct epsilon=0.2 curved divergence and correct "
                    "curved analytic RHS as references"
                ),
                "normalized_discrepancy_definition": (
                    "space-time combined RMS(defective y-mode identity result "
                    "minus correct curved analytic RHS) divided by max(space-time "
                    "combined RMS correct curved analytic RHS,epsilon_control)"
                ),
                "minimum_normalized_discrepancy": 0.02,
            },
        },
        "required_controls": {
            "analytic_warped_product_curvature_route": True,
            "independent_generic_tensor_curvature_route": True,
            "curvature_route_agreement": True,
            "spatially_varying_nonzero_curvature": True,
            "metric_compatibility": True,
            "on_shell_temporal_mode": True,
            "off_shell_y_mode": True,
            "off_shell_x_mode": True,
            "all_three_divergence_components": True,
            "all_five_negative_controls": True,
            "flat_limit_recovery": True,
            "grid_refinement": True,
            "componentwise_and_combined_norms": True,
            "deterministic_reexecution": True,
            "complete_hash_manifest": True,
        },
        "success_criteria": {
            **FROZEN_SUCCESS_CRITERIA,
            "all_thresholds_required": True,
        },
        "threshold_decisions": [
            dict(decision) for decision in FROZEN_THRESHOLD_DECISIONS
        ],
        "success_criteria_definitions": {
            "maximum_analytic_profile_residual_reference_error": (
                "maximum discrepancy between each frozen explicit residual "
                "formula and -phi_tt+phi_xx+(f'/f)phi_x+f^(-2)phi_yy-m^2*phi "
                "assembled independently from analytic derivatives; this is not "
                "a finite-difference Box_g residual"
            ),
            "two_finest_convergence_decision": (
                "p_min=min(log2(error_64/error_128),"
                "log2(error_128/error_256)); one decision per off-shell mode"
            ),
            "negative_control_threshold_policy": (
                "each of the five negative controls has its own frozen threshold "
                "and must pass individually; multi-profile controls use the "
                "minimum profile-specific result and no aggregate can mask a failure"
            ),
            "negative_control_resolution_adjudication": (
                "report every frozen resolution; adjudicate each negative-control "
                "threshold on the finest frozen grid N=256"
            ),
        },
        "failure_criteria": {
            "any_threshold_failure": True,
            "primary_claim_label": "B-BLOCKED",
            "selected_diagnostic_target": DIAGNOSTIC_FAILURE_TARGET,
            "failed_artifacts_preserved": True,
            "threshold_changes_require_new_versioned_guardrail": True,
            "threshold_relaxation_in_this_version_forbidden": True,
            "diagnostic_priorities": [
                "analytic_reference_error",
                "implementation_defect",
                "stencil_or_axis_defect",
                "periodic_boundary_handling_defect",
                "model_or_profile_problem",
                "inadequate_resolution",
            ],
            "control_aggregation_cannot_hide_individual_failure": True,
        },
        "allowed_operations": [
            "evaluate the fixed metric, inverse metric, determinant, and connection",
            "reconstruct curvature through both frozen independent routes",
            "evaluate analytic temporal and metric derivatives",
            "apply second-order centered periodic x and y differences",
            "compute nu=0, nu=1, and nu=2 covariant divergence components",
            "run the three frozen field profiles",
            "run the positive flat limit and five frozen negative controls",
            "compute componentwise, combined, and space-time RMS norms",
            "write deterministic canonical result, manifest, and report artifacts",
        ],
        "forbidden_claims": [
            "general curved-spacetime theorem",
            "gravity evolution or Einstein-equation solution",
            "Einstein-source compatibility or source admissibility",
            "Bianchi compatibility",
            "QFT-GR seam admissibility or closure",
            "local propagating gravitational-wave validation in 2+1 dimensions",
            "quantum or renormalized stress-energy source",
            "pillar completion or Level 4 promotion",
            "CCFT validation or resumption",
            "master-action canonicalization, promotion, or closure",
        ],
        "assumptions": [
            "fixed prescribed 2+1-dimensional warped periodic background",
            "real massive minimally coupled scalar",
            "f(x)=1+0.2*cos(x) remains positive throughout the domain",
            "periodic x and y boundaries",
            "analytic metric, connection, curvature reference, and time derivatives",
            "second-order numerical spatial derivatives",
            "no metric evolution and no Einstein-equation solve",
            "2+1 Einstein gravity has no local propagating gravitational-wave modes",
        ],
        "units": {
            "convention": "dimensionless numerical test units with c = hbar = 1",
            "coordinate_parameter_consistency": (
                "t, x, y, m, omega, k, and ell use one natural-unit normalization"
            ),
            "physical_parameter_inference_allowed": False,
        },
        "outputs": {
            "result": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-"
                "DIVERGENCE-IDENTITY-HIGHER-DIMENSIONAL-CURVED-BACKGROUND-v0.json"
            ),
            "manifest": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-"
                "DIVERGENCE-IDENTITY-HIGHER-DIMENSIONAL-CURVED-BACKGROUND-"
                "MANIFEST-v0.json"
            ),
            "execution_report": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
                "IDENTITY_HIGHER_DIMENSIONAL_CURVED_BACKGROUND_CALCULATION_"
                "EXECUTION_20260709_v0.json"
            ),
        },
        "claim_ceiling": {
            "claim_ladder_level": 3,
            "classification": "toy-model demonstration",
            "e_repro_status": "pending_execution_and_independent_result_review",
            "scope": "one fixed 2+1 warped-background scalar matter identity only",
            "not_general_curved_spacetime_theorem": True,
            "not_gravity_dynamics": True,
            "not_einstein_source_compatibility": True,
            "not_source_admissibility": True,
            "not_bianchi_compatibility": True,
            "not_qft_gr_seam_admissibility_or_closure": True,
            "not_level_4_or_level_5_promotion": True,
            "not_master_action_promotion": True,
        },
        "boundary": {
            "fixed_background_matter_identity_only": True,
            "spacetime_dimension": 3,
            "two_dimensional_Einstein_degeneracy_not_applicable": True,
            "einstein_tensor_can_be_nonzero": True,
            "background_fixed": True,
            "Einstein_source_tested": False,
            "einstein_tensor_source_tested": False,
            "gravity_evolved": False,
            "general_covariant_conservation_claimed": False,
            "source_admissibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "level_4_claimed": False,
            "level_5_claimed": False,
            "pillar_completion_claimed": False,
            "ccft_resumed": False,
            "master_action_promoted": False,
        },
        "reproduction_command": (
            "python -m formal.python.toe.calculations."
            "calc_scalar_stress_energy_covariant_divergence_identity_higher_"
            "dimensional_curved_background"
        ),
        "canonical_json_contract": {
            "encoding": "UTF-8 without BOM",
            "newline": "LF",
            "object_keys": "sorted",
            "separators": [",", ":"],
            "ensure_ascii": True,
            "allow_nan": False,
            "array_order": "preserved",
            "trailing_newline": "exactly one LF",
        },
        "calculation_executed": False,
        "e_repro_claimed_by_guardrail": False,
        "equation_compendium_row_added": False,
        "ccft_lane_status": "paused_upstream_prerequisites",
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def validate_guardrail_payload(payload: dict[str, Any]) -> None:
    required_interface = {
        "supersession",
        "question",
        "inputs",
        "background_geometry",
        "connection_and_curvature_conventions",
        "curvature_verification",
        "equation_surfaces",
        "solution_controls",
        "numerical_method",
        "flat_limit_control",
        "negative_controls",
        "success_criteria",
        "threshold_decisions",
        "success_criteria_definitions",
        "failure_criteria",
        "outputs",
        "claim_ceiling",
        "boundary",
        "reproduction_command",
        "required_controls",
        "assumptions",
        "units",
        "allowed_operations",
        "forbidden_claims",
        "canonical_json_contract",
    }
    if not required_interface.issubset(payload):
        raise ValueError("guardrail is missing required sprint interface fields")
    if (
        payload.get("schema_id") != PACKET_SCHEMA_ID
        or payload.get("packet_id") != PACKET_ID
        or payload.get("captured_at_utc") != CAPTURED_AT_UTC
        or payload.get("revised_at_utc") != REVISED_AT_UTC
        or payload.get("consumed_target") != GUARDRAIL_TARGET
        or payload.get("selected_next_target") != EXECUTION_TARGET
        or payload.get("packet_result") != GUARDRAIL_OUTCOME
        or payload.get("strict_packet_result") != GUARDRAIL_STRICT_OUTCOME
    ):
        raise ValueError("guardrail lifecycle or outcome differs from frozen values")
    supersession = payload.get("supersession", {})
    if (
        supersession.get("supersedes_schema_id") != SUPERSEDED_PACKET_SCHEMA_ID
        or supersession.get("supersedes_packet_id") != SUPERSEDED_PACKET_ID
        or supersession.get("supersedes_sha256")
        != EXPECTED_SUPERSEDED_GUARDRAIL_SHA256
        or supersession.get("superseded_artifact_preserved_byte_for_byte")
        is not True
        or _verified_superseded_guardrail_hash()
        != EXPECTED_SUPERSEDED_GUARDRAIL_SHA256
    ):
        raise ValueError("guardrail v0 supersession or byte preservation differs")
    if payload.get("accepted_predecessor", {}).get("sha256") != (
        EXPECTED_PREDECESSOR_REVIEW_SHA256
    ):
        raise ValueError("guardrail predecessor hash differs")
    if payload.get("readiness_authority", {}).get("sha256") != (
        EXPECTED_READINESS_SHA256
    ):
        raise ValueError("guardrail readiness-authority hash differs")

    inputs = payload["inputs"]
    geometry = payload["background_geometry"]
    if (
        inputs.get("spacetime_dimension") != 3
        or inputs.get("dimension_label") != "2+1"
        or inputs.get("warp_amplitude_epsilon") != 0.2
        or inputs.get("warp_factor_minimum") != 0.8
        or inputs.get("warp_factor_maximum") != 1.2
        or inputs.get("spatial_resolutions_Nx_equals_Ny")
        != SPATIAL_RESOLUTIONS
        or inputs.get("time_slices") != TIME_SLICES
        or inputs.get("resolution_symbol_N_means") != "N x N spatial grid"
        or inputs.get("periodic_endpoint_duplicated") is not False
        or inputs.get("maximum_inverse_y_metric_factor") != 1.5625
        or inputs.get("minimum_absolute_metric_determinant") != 0.64
    ):
        raise ValueError("2+1 warped-background inputs differ")
    if (
        geometry.get("classification") != BACKGROUND_GEOMETRY_CLASSIFICATION
        or geometry.get("metric_signature") != "(-,+,+)"
        or geometry.get("metric") != "g_mu_nu = diag(-1, 1, f(x)^2)"
        or geometry.get("inverse_metric")
        != "g^mu_nu = diag(-1, 1, f(x)^(-2))"
        or geometry.get("determinant") != "det(g_mu_nu) = -f(x)^2"
        or geometry.get("volume_density")
        != "sqrt(-g) = f(x), because f(x) >= 0.8"
        or geometry.get("scalar_curvature")
        != (
            "R(x) = -2*f''(x)/f(x) = "
            "2*epsilon*cos(x)/(1+epsilon*cos(x))"
        )
        or geometry.get("scalar_curvature_minimum") != -0.5
        or geometry.get("scalar_curvature_maximum")
        != 0.3333333333333333
        or geometry.get("curvature_spatially_varying") is not True
        or geometry.get("curvature_zero_crossings_exact")
        != ["pi/2", "3*pi/2"]
        or geometry.get("gravity_evolved") is not False
    ):
        raise ValueError("geometry contract differs")

    conventions = payload["connection_and_curvature_conventions"]
    if conventions.get("nonzero_christoffels") != {
        "Gamma^x_{y y}": "-f(x)*f'(x)",
        "Gamma^y_{x y}": "f'(x)/f(x)",
        "Gamma^y_{y x}": "f'(x)/f(x)",
    }:
        raise ValueError("Christoffel contract differs")
    if (
        conventions.get("einstein_tensor_not_identically_zero") is not True
        or conventions.get("einstein_tensor_source_tested") is not False
    ):
        raise ValueError("Einstein-tensor boundary differs")
    curvature = payload["curvature_verification"]
    if (
        curvature.get("analytic_warped_product_route", {}).get("formula")
        != "R_analytic(x) = -2*f''(x)/f(x)"
        or curvature.get("independent_generic_tensor_route", {}).get("route")
        != [
            "metric",
            "inverse_metric",
            "metric_derivatives",
            "Christoffel_symbols",
            "Riemann_tensor",
            "Ricci_tensor",
            "scalar_contraction",
        ]
        or "do not call" not in curvature.get(
            "independent_generic_tensor_route", {}
        ).get("implementation_independence", "")
        or curvature.get("maximum_route_agreement_absolute_error") != 1e-12
        or curvature.get("minimum_peak_absolute_scalar_curvature") != 0.49
        or curvature.get("minimum_peak_to_peak_scalar_curvature") != 0.8
    ):
        raise ValueError("independent curvature-route contract differs")
    zero_policy = curvature.get("curvature_zero_exclusion_policy", {})
    if (
        zero_policy.get("epsilon_R") != EPSILON_R
        or zero_policy.get("absolute_error_reported_at_every_x_index") is not True
        or zero_policy.get("excluded_relative_error_value") is not None
        or zero_policy.get("excluded_status") != "excluded_near_zero"
        or zero_policy.get("non_gating_reporting_rule") is not True
        or zero_policy.get("not_an_additional_success_threshold") is not True
        or zero_policy.get("exact_crossing_locations")
        != ["pi/2", "3*pi/2"]
        or zero_policy.get("per_resolution_exclusions")
        != [
            {
                "resolution_N": resolution,
                "excluded_x_index_count": 2,
                "excluded_x_indices": [resolution // 4, 3 * resolution // 4],
                "excluded_spatial_gridpoint_count": 2 * resolution,
            }
            for resolution in SPATIAL_RESOLUTIONS
        ]
    ):
        raise ValueError("curvature-zero exclusion reporting contract differs")

    equations = payload["equation_surfaces"]
    if (
        equations.get("divergence_components_required") != [0, 1, 2]
        or equations.get("potential_derivative") != "V'(phi) = m^2 phi"
        or equations.get("volume_trace_connection_term")
        != "Gamma^mu_{mu lambda} T^{lambda nu}"
        or equations.get("tensor_index_connection_term")
        != "Gamma^nu_{mu lambda} T^{mu lambda}"
        or equations.get("analytic_profile_residual_reference_assembly")
        != (
            "-phi_tt + phi_xx + [f'(x)/f(x)]*phi_x + "
            "f(x)^(-2)*phi_yy - m^2*phi"
        )
        or equations.get("analytic_profile_residual_reference_metric")
        != "maximum_analytic_profile_residual_reference_error"
        or equations.get("existing_equation_id_reused") != EQUATION_ID
        or equations.get("existing_equation_status")
        != "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"
        or equations.get("new_equation_identity_created") is not False
        or equations.get("equation_surface_upgraded") is not False
        or equations.get("equation_compendium_edited") is not False
    ):
        raise ValueError("equation-surface contract differs")
    profiles = payload["solution_controls"]
    if set(profiles) != {
        "on_shell_temporal_mode",
        "off_shell_y_mode",
        "off_shell_x_mode",
    }:
        raise ValueError("field-profile contract differs")
    if (
        profiles["on_shell_temporal_mode"].get("parameters")
        != {"A": 0.2, "m": 1.0}
        or profiles["on_shell_temporal_mode"].get("exact_residual")
        != "E_phi = 0"
        or profiles["off_shell_y_mode"].get("parameters")
        != {"A": 0.2, "omega_y": 1.5, "ell": 2}
        or profiles["off_shell_y_mode"].get("exact_residual")
        != "E_phi = [omega_y^2-m^2-ell^2/f(x)^2]*phi_y"
        or profiles["off_shell_y_mode"].get("substituted_exact_residual")
        != "E_phi = [1.25-4/f(x)^2]*phi_y"
        or profiles["off_shell_x_mode"].get("parameters")
        != {"A": 0.2, "omega_x": 1.7, "k": 2}
        or profiles["off_shell_x_mode"].get("exact_residual")
        != (
            "E_phi = (omega_x^2-m^2-k^2)*phi_x - "
            "A*k*[f'(x)/f(x)]*cos(omega_x*t)*sin(k*x)"
        )
    ):
        raise ValueError("analytic field residual contract differs")

    if set(payload["negative_controls"]) != NEGATIVE_CONTROL_IDS:
        raise ValueError("exactly five frozen negative controls are required")
    method = payload["numerical_method"]
    if (
        method.get("refinement_schedule")
        != {
            "Nx_equals_Ny": SPATIAL_RESOLUTIONS,
            "delta_x_equals_delta_y": "2*pi/N",
            "refinement_ratio": 2,
        }
        or method.get("convergence_profiles")
        != ["off_shell_y_mode", "off_shell_x_mode"]
        or "periodic" not in method.get("spatial_discretization", "")
        or "sum_{nu=0}^2" not in method.get(
            "combined_rms_norm_at_each_time", ""
        )
        or method.get("norm_contract")
        != {
            "name": COORDINATE_GRID_NORM_NAME,
            "coordinate_grid_uniform_unweighted": True,
            "coordinate_invariant_tensor_norm": False,
            "curved_volume_weighted": False,
            "epsilon_norm": EPSILON_NORM,
            "epsilon_control": EPSILON_CONTROL,
            "component_rms": "sqrt(mean(error_nu^2))",
            "combined_rms": "sqrt(mean(error_t^2+error_x^2+error_y^2))",
            "off_shell_component_relative_error": (
                "RMS(divergence_nu-RHS_nu)/max(RMS(RHS_nu),epsilon_norm)"
            ),
            "control_error_ratio": (
                "defective_error/max(correct_error,epsilon_control)"
            ),
            "normalized_defect_discrepancy": (
                "RMS(defective-correct_curved_RHS)/"
                "max(RMS(correct_curved_RHS),epsilon_control)"
            ),
        }
        or method.get("convergence_gate", {}).get("p_min")
        != "min(p_64_128,p_128_256)"
        or method.get("convergence_gate", {}).get(
            "component_orders_diagnostic_only"
        )
        is not True
    ):
        raise ValueError("numerical refinement or norm contract differs")
    flat = payload["flat_limit_control"]
    if (
        flat.get("positive_control", {}).get("substitution")
        != "epsilon -> 0, hence f -> 1"
        or flat.get("positive_control", {}).get("expected_scalar_curvature") != 0.0
        or flat.get("positive_control", {}).get("operator_coefficients_exact")
        != [-1, 1, 1]
        or flat.get("positive_control", {}).get("maximum_numeric_discrepancy")
        != 1e-11
        or flat.get("positive_control", {}).get(
            "independent_floating_route_byte_equality_required"
        )
        is not False
        or "changes both geometry and analytic reference"
        not in flat.get("distinct_from_negative_control", "")
    ):
        raise ValueError("positive flat-limit contract differs")
    criteria = payload["success_criteria"]
    if criteria != {**FROZEN_SUCCESS_CRITERIA, "all_thresholds_required": True}:
        raise ValueError("success-threshold set or value differs")
    decisions = payload["threshold_decisions"]
    if (
        decisions != FROZEN_THRESHOLD_DECISIONS
        or [item.get("decision_number") for item in decisions]
        != list(range(1, 17))
        or {item.get("threshold_id") for item in decisions} != THRESHOLD_IDS
        or any(
            item.get("threshold")
            != FROZEN_SUCCESS_CRITERIA[item["threshold_id"]]
            for item in decisions
        )
    ):
        raise ValueError("exact sixteen threshold decisions differ")
    negative = payload["negative_controls"]
    if (
        negative["naive_partial_divergence"].get(
            "minimum_error_ratio_to_correct_covariant_result"
        )
        != FROZEN_SUCCESS_CRITERIA[
            "minimum_naive_partial_divergence_error_ratio"
        ]
        or negative["omitted_tensor_index_connection_term"].get(
            "minimum_error_ratio_to_correct_covariant_result"
        )
        != FROZEN_SUCCESS_CRITERIA[
            "minimum_omitted_tensor_index_term_error_ratio"
        ]
        or negative["omitted_volume_trace_connection_term"].get(
            "minimum_error_ratio_to_correct_covariant_result"
        )
        != FROZEN_SUCCESS_CRITERIA[
            "minimum_omitted_volume_trace_term_error_ratio"
        ]
        or negative["curved_case_flat_geometry_substitution"].get(
            "minimum_normalized_discrepancy"
        )
        != FROZEN_SUCCESS_CRITERIA[
            "minimum_flat_geometry_substitution_normalized_discrepancy"
        ]
        or negative["incorrect_y_inverse_metric_factor"].get(
            "minimum_normalized_discrepancy"
        )
        != FROZEN_SUCCESS_CRITERIA[
            "minimum_incorrect_y_inverse_metric_normalized_discrepancy"
        ]
    ):
        raise ValueError("negative-control threshold differs")
    if (
        "minimum of the two profile-specific ratios"
        not in negative["naive_partial_divergence"].get("evaluation", "")
        or "max(space-time combined RMS correct covariant identity error,epsilon_control)"
        not in negative["naive_partial_divergence"].get(
            "ratio_definition", ""
        )
        or any(
            "max(correct on-shell combined absolute divergence error,epsilon_control)"
            not in negative[control].get("ratio_definition", "")
            for control in (
                "omitted_tensor_index_connection_term",
                "omitted_volume_trace_connection_term",
            )
        )
        or "minimum profile-specific normalized discrepancy"
        not in negative["curved_case_flat_geometry_substitution"].get(
            "evaluation", ""
        )
        or "correct curved analytic RHS,epsilon_control"
        not in negative["curved_case_flat_geometry_substitution"].get(
            "normalized_discrepancy_definition", ""
        )
        or "correct curved analytic RHS,epsilon_control"
        not in negative["incorrect_y_inverse_metric_factor"].get(
            "normalized_discrepancy_definition", ""
        )
    ):
        raise ValueError("negative-control norm or adjudication policy differs")
    if not payload["required_controls"] or not all(
        value is True for value in payload["required_controls"].values()
    ):
        raise ValueError("every required control must be frozen true")
    failure = payload["failure_criteria"]
    if (
        failure.get("selected_diagnostic_target") != DIAGNOSTIC_FAILURE_TARGET
        or "selected_repair_target" in failure
        or failure.get("threshold_changes_require_new_versioned_guardrail")
        is not True
        or failure.get("threshold_relaxation_in_this_version_forbidden")
        is not True
    ):
        raise ValueError("diagnostic failure lifecycle differs")
    if (
        not payload["assumptions"]
        or not payload["allowed_operations"]
        or not payload["forbidden_claims"]
        or payload["units"].get("physical_parameter_inference_allowed") is not False
    ):
        raise ValueError("scope, operation, or units contract differs")
    if payload["canonical_json_contract"] != {
        "encoding": "UTF-8 without BOM",
        "newline": "LF",
        "object_keys": "sorted",
        "separators": [",", ":"],
        "ensure_ascii": True,
        "allow_nan": False,
        "array_order": "preserved",
        "trailing_newline": "exactly one LF",
    }:
        raise ValueError("canonical JSON contract differs")

    claim = payload["claim_ceiling"]
    if claim.get("claim_ladder_level") != 3:
        raise ValueError("guardrail claim ceiling must remain Level 3")
    for key in (
        "not_general_curved_spacetime_theorem",
        "not_gravity_dynamics",
        "not_einstein_source_compatibility",
        "not_source_admissibility",
        "not_bianchi_compatibility",
        "not_qft_gr_seam_admissibility_or_closure",
        "not_level_4_or_level_5_promotion",
        "not_master_action_promotion",
    ):
        if claim.get(key) is not True:
            raise ValueError(f"claim ceiling lost required nonclaim: {key}")
    boundary = payload["boundary"]
    if (
        boundary.get("spacetime_dimension") != 3
        or boundary.get("two_dimensional_Einstein_degeneracy_not_applicable")
        is not True
        or boundary.get("einstein_tensor_can_be_nonzero") is not True
        or boundary.get("background_fixed") is not True
        or boundary.get("Einstein_source_tested") is not False
        or boundary.get("einstein_tensor_source_tested") is not False
        or boundary.get("gravity_evolved") is not False
        or boundary.get("bianchi_compatibility_claimed") is not False
        or boundary.get("qft_gr_seam_admissibility_claimed") is not False
        or boundary.get("master_action_promoted") is not False
        or payload.get("calculation_executed") is not False
        or payload.get("e_repro_claimed_by_guardrail") is not False
        or payload.get("equation_compendium_row_added") is not False
    ):
        raise ValueError("guardrail overclaims or records premature execution")
    if payload != build_guardrail_payload():
        raise ValueError("guardrail payload differs from the exact frozen contract")
    canonical_json_bytes(payload)


def write_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(report_json_bytes(payload))


def guardrail_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the fixed 2+1 warped curved-background scalar guardrail."
        )
    )
    parser.add_argument("--out", type=Path, default=GUARDRAIL_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "background_geometry_classification": (
                    BACKGROUND_GEOMETRY_CLASSIFICATION
                ),
                "negative_control_count": len(payload["negative_controls"]),
                "outcome": GUARDRAIL_OUTCOME,
                "selected_next_target": EXECUTION_TARGET,
                "threshold_count": len(payload["success_criteria"]) - 1,
            },
            sort_keys=True,
        )
    )
    return 0


def _reject_nonfinite_json(token: str) -> None:
    raise ValueError(f"non-finite JSON token: {token}")


def _reject_duplicate_object_pairs(
    pairs: list[tuple[str, Any]],
) -> dict[str, Any]:
    payload: dict[str, Any] = {}
    for key, value in pairs:
        if key in payload:
            raise ValueError(f"duplicate JSON object key: {key}")
        payload[key] = value
    return payload


def _load_strict_json_object(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    if raw.startswith(b"\xef\xbb\xbf"):
        raise ValueError(f"UTF-8 BOM is forbidden: {path}")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"artifact is not valid UTF-8: {path}") from error
    try:
        payload = json.loads(
            text,
            parse_constant=_reject_nonfinite_json,
            object_pairs_hook=_reject_duplicate_object_pairs,
        )
    except json.JSONDecodeError as error:
        raise ValueError(f"artifact is not valid strict JSON: {path}") from error
    if not isinstance(payload, dict):
        raise ValueError(f"expected a JSON object at {path}")
    canonical_json_bytes(payload)
    return payload


def _require_exact_keys(
    payload: dict[str, Any], expected: set[str], label: str
) -> None:
    actual = set(payload)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        raise ValueError(
            f"{label} fields differ; missing={missing}, extra={extra}"
        )


def _expected_execution_thresholds() -> dict[str, float | bool]:
    return {"all_thresholds_required": True, **FROZEN_SUCCESS_CRITERIA}


def _recompute_execution_threshold_checks(
    result: dict[str, Any],
) -> dict[str, bool]:
    evidence = result["threshold_evidence"]
    thresholds = result["thresholds"]
    controls = result["negative_controls"]["finest_resolution_adjudication"]
    return {
        "minimum_two_finest_x_mode_convergence_order": (
            evidence["minimum_two_finest_x_mode_convergence_order"]
            >= thresholds["minimum_two_finest_x_mode_convergence_order"]
        ),
        "minimum_two_finest_y_mode_convergence_order": (
            evidence["minimum_two_finest_y_mode_convergence_order"]
            >= thresholds["minimum_two_finest_y_mode_convergence_order"]
        ),
        "maximum_finest_x_mode_combined_relative_identity_error": (
            evidence["finest_x_mode_combined_relative_identity_error"]
            <= thresholds[
                "maximum_finest_x_mode_combined_relative_identity_error"
            ]
        ),
        "maximum_finest_y_mode_combined_relative_identity_error": (
            evidence["finest_y_mode_combined_relative_identity_error"]
            <= thresholds[
                "maximum_finest_y_mode_combined_relative_identity_error"
            ]
        ),
        "maximum_finest_on_shell_combined_absolute_divergence_error": (
            evidence["finest_on_shell_combined_absolute_divergence_error"]
            <= thresholds[
                "maximum_finest_on_shell_combined_absolute_divergence_error"
            ]
        ),
        "maximum_analytic_profile_residual_reference_error": (
            evidence["maximum_analytic_profile_residual_reference_error"]
            <= thresholds[
                "maximum_analytic_profile_residual_reference_error"
            ]
        ),
        "maximum_metric_compatibility_absolute_error": (
            evidence["maximum_metric_compatibility_absolute_error"]
            <= thresholds["maximum_metric_compatibility_absolute_error"]
        ),
        "maximum_curvature_route_absolute_discrepancy": (
            evidence["maximum_curvature_route_absolute_discrepancy"]
            <= thresholds["maximum_curvature_route_absolute_discrepancy"]
        ),
        "minimum_curvature_peak_absolute_value": (
            evidence["peak_absolute_scalar_curvature"]
            >= thresholds["minimum_curvature_peak_absolute_value"]
        ),
        "minimum_curvature_peak_to_peak_variation": (
            evidence["curvature_peak_to_peak_variation"]
            >= thresholds["minimum_curvature_peak_to_peak_variation"]
        ),
        "maximum_flat_limit_absolute_discrepancy": (
            evidence["maximum_flat_limit_absolute_discrepancy"]
            <= thresholds["maximum_flat_limit_absolute_discrepancy"]
        ),
        "minimum_naive_partial_divergence_error_ratio": controls[
            "naive_partial_divergence"
        ]["pass"],
        "minimum_omitted_tensor_index_term_error_ratio": controls[
            "omitted_tensor_index_connection_term"
        ]["pass"],
        "minimum_omitted_volume_trace_term_error_ratio": controls[
            "omitted_volume_trace_connection_term"
        ]["pass"],
        "minimum_flat_geometry_substitution_normalized_discrepancy": controls[
            "curved_case_flat_geometry_substitution"
        ]["pass"],
        "minimum_incorrect_y_inverse_metric_normalized_discrepancy": controls[
            "incorrect_y_inverse_metric_factor"
        ]["pass"],
    }


def _validate_identity_metric(metric: dict[str, Any], *, label: str) -> None:
    _require_exact_keys(
        metric,
        {
            "value_rms",
            "reference_rms",
            "absolute_error_rms",
            "relative_error",
            "relative_error_applicable",
            "convergence_status",
        },
        label,
    )
    if metric["reference_rms"] == 0.0:
        if (
            metric["relative_error"] is not None
            or metric["relative_error_applicable"] is not False
            or metric["convergence_status"]
            != "not_applicable_exact_zero"
        ):
            raise ValueError(f"{label} forms a relative error against zero")
    elif (
        metric["relative_error_applicable"] is not True
        or metric["relative_error"] is None
        or metric["convergence_status"] != "reported_separately"
    ):
        raise ValueError(f"{label} loses the nonzero-reference error policy")


def _validate_identity_metrics(metrics: dict[str, Any], *, label: str) -> None:
    _require_exact_keys(metrics, {"components", "combined"}, label)
    components = metrics["components"]
    if set(components) != {"nu_t", "nu_x", "nu_y"}:
        raise ValueError(f"{label} does not contain all three components")
    for component, metric in components.items():
        _validate_identity_metric(metric, label=f"{label}.{component}")
    _validate_identity_metric(metrics["combined"], label=f"{label}.combined")


def _validate_result_rows(result: dict[str, Any]) -> None:
    rows = result["profile_time_resolution_rows"]
    aggregates = result["profile_resolution_aggregates"]
    if result["profile_time_resolution_row_count"] != 36 or len(rows) != 36:
        raise ValueError("execution must contain exactly 36 profile/time rows")
    if (
        result["profile_resolution_aggregate_count"] != 12
        or len(aggregates) != 12
    ):
        raise ValueError("execution must contain exactly 12 profile aggregates")
    expected_rows = {
        (profile, resolution, time)
        for profile in (
            "on_shell_temporal_mode",
            "off_shell_x_mode",
            "off_shell_y_mode",
        )
        for resolution in SPATIAL_RESOLUTIONS
        for time in TIME_SLICES
    }
    observed_rows: set[tuple[str, int, float]] = set()
    for row in rows:
        key = (row["profile_id"], row["resolution_N"], row["time_t"])
        observed_rows.add(key)
        if row["grid_shape"] != [row["resolution_N"], row["resolution_N"]]:
            raise ValueError("profile/time row grid is not N x N")
        if row["norm_name"] != COORDINATE_GRID_NORM_NAME:
            raise ValueError("profile/time row norm differs")
        _validate_identity_metrics(
            row["identity_metrics"], label=f"profile/time row {key}"
        )
    if observed_rows != expected_rows:
        raise ValueError("profile/time row axes or ordering members differ")
    expected_aggregates = {
        (profile, resolution)
        for profile in (
            "on_shell_temporal_mode",
            "off_shell_x_mode",
            "off_shell_y_mode",
        )
        for resolution in SPATIAL_RESOLUTIONS
    }
    observed_aggregates: set[tuple[str, int]] = set()
    for aggregate in aggregates:
        key = (aggregate["profile_id"], aggregate["resolution_N"])
        observed_aggregates.add(key)
        if (
            aggregate["grid_shape"]
            != [aggregate["resolution_N"], aggregate["resolution_N"]]
            or aggregate["time_slice_count"] != 3
            or aggregate["time_slices"] != TIME_SLICES
            or aggregate["norm_name"] != COORDINATE_GRID_NORM_NAME
        ):
            raise ValueError("profile aggregate axes or norm differ")
        _validate_identity_metrics(
            aggregate["identity_metrics"], label=f"profile aggregate {key}"
        )
    if observed_aggregates != expected_aggregates:
        raise ValueError("profile aggregate members differ")


def _validate_curvature_zero_reporting(result: dict[str, Any]) -> None:
    geometry = result["geometry_verification"]
    diagnostics = geometry["resolution_diagnostics"]
    if [row["resolution_N"] for row in diagnostics] != SPATIAL_RESOLUTIONS:
        raise ValueError("curvature diagnostics resolutions differ")
    for row in diagnostics:
        resolution = row["resolution_N"]
        excluded = [resolution // 4, 3 * resolution // 4]
        if (
            row["relative_error_cutoff_epsilon_R"] != EPSILON_R
            or row["excluded_x_index_count"] != 2
            or row["excluded_x_indices"] != excluded
            or row["excluded_spatial_gridpoint_count"] != 2 * resolution
            or row["crossing_locations"]
            != [1.5707963267948966, 4.71238898038469]
            or len(row["x_index_error_rows"]) != resolution
        ):
            raise ValueError("curvature-zero exclusion metadata differs")
        by_index = {entry["x_index"]: entry for entry in row["x_index_error_rows"]}
        for index in excluded:
            entry = by_index[index]
            if (
                entry["relative_error"] is not None
                or entry["status"] != "excluded_near_zero"
            ):
                raise ValueError("curvature crossing forms a relative error")
        for index in set(range(resolution)) - set(excluded):
            entry = by_index[index]
            if (
                entry["relative_error"] is None
                or entry["status"] != "reported"
            ):
                raise ValueError("away-from-zero curvature error was excluded")
    if geometry["curvature_zero_reporting_is_non_gating"] is not True:
        raise ValueError("curvature-zero reporting cutoff became a gate")


def _validate_negative_controls(result: dict[str, Any]) -> None:
    negative = result["negative_controls"]
    records = negative["records"]
    if negative["record_count"] != 20 or len(records) != 20:
        raise ValueError("execution must contain 20 negative-control records")
    expected_operations = {
        "naive_partial_divergence": (
            "omit both Gamma^mu_mu_lambda T^lambda_nu and "
            "Gamma^nu_mu_lambda T^mu_lambda"
        ),
        "omitted_tensor_index_connection_term": (
            "omit only Gamma^nu_mu_lambda T^mu_lambda"
        ),
        "omitted_volume_trace_connection_term": (
            "omit only Gamma^mu_mu_lambda T^lambda_nu"
        ),
        "curved_case_flat_geometry_substitution": (
            "set epsilon=0 in metric,inverse metric,connection,stress,and "
            "divergence while retaining the epsilon=0.2 curved RHS"
        ),
        "incorrect_y_inverse_metric_factor": (
            "replace g^yy=f^-2 by g^yy=1 in the defective y residual and "
            "raised y-gradient while retaining the correct curved references"
        ),
    }
    expected_members = {
        (control_id, resolution)
        for control_id in NEGATIVE_CONTROL_IDS
        for resolution in SPATIAL_RESOLUTIONS
    }
    observed_members: set[tuple[str, int]] = set()
    record_by_member: dict[tuple[str, int], dict[str, Any]] = {}
    for record in records:
        key = (record["control_id"], record["resolution_N"])
        observed_members.add(key)
        record_by_member[key] = record
        if record["exact_defective_operation"] != expected_operations[key[0]]:
            raise ValueError("negative-control defective operation differs")
        expected_pass = record["comparison_value"] >= record["threshold"]
        if record["comparison"] != ">=" or record["pass"] is not expected_pass:
            raise ValueError("negative-control record adjudication differs")
    if observed_members != expected_members or len(record_by_member) != 20:
        raise ValueError("negative-control ids or resolutions differ")
    adjudication = negative["finest_resolution_adjudication"]
    if set(adjudication) != NEGATIVE_CONTROL_IDS | {
        "all_five_negative_controls_passed"
    }:
        raise ValueError("finest negative-control adjudication fields differ")
    for control_id in NEGATIVE_CONTROL_IDS:
        source = record_by_member[(control_id, 256)]
        summary = adjudication[control_id]
        if summary != {
            "resolution_N": 256,
            "comparison_value": source["comparison_value"],
            "threshold": source["threshold"],
            "pass": source["pass"],
        }:
            raise ValueError("finest negative-control adjudication differs")
    combined = all(adjudication[name]["pass"] for name in NEGATIVE_CONTROL_IDS)
    if adjudication["all_five_negative_controls_passed"] is not combined:
        raise ValueError("combined control status masks an individual control")


def _validate_convergence_diagnostics(result: dict[str, Any]) -> None:
    diagnostics = result["convergence_diagnostics"]
    if set(diagnostics) != {
        "on_shell_temporal_mode",
        "off_shell_x_mode",
        "off_shell_y_mode",
    }:
        raise ValueError("convergence profile set differs")
    for profile_id, profile in diagnostics.items():
        if set(profile) != {"nu_t", "nu_x", "nu_y", "combined"}:
            raise ValueError("convergence component set differs")
        for component, metric in profile.items():
            if len(metric["errors"]) != 4:
                raise ValueError("convergence error schedule differs")
            if metric["convergence_status"] == "not_applicable_exact_zero":
                if (
                    metric["orders"] != []
                    or metric["minimum_two_finest_order"] is not None
                    or metric["p_64_128"] is not None
                    or metric["p_128_256"] is not None
                    or metric["p_min"] is not None
                ):
                    raise ValueError("exact-zero convergence was fabricated")
                continue
            if metric["convergence_status"] != "reported":
                raise ValueError("convergence status differs")
            orders = metric["orders"]
            if len(orders) != 3:
                raise ValueError("convergence refinement-pair count differs")
            p_64_128 = orders[1]["order"]
            p_128_256 = orders[2]["order"]
            p_min = min(p_64_128, p_128_256)
            if (
                metric["p_64_128"] != p_64_128
                or metric["p_128_256"] != p_128_256
                or metric["p_min"] != p_min
                or metric["minimum_two_finest_order"] != p_min
            ):
                raise ValueError("two-finest-pair convergence metadata differs")
    evidence = result["threshold_evidence"]
    if (
        diagnostics["off_shell_x_mode"]["combined"]["p_min"]
        != evidence["minimum_two_finest_x_mode_convergence_order"]
        or diagnostics["off_shell_y_mode"]["combined"]["p_min"]
        != evidence["minimum_two_finest_y_mode_convergence_order"]
    ):
        raise ValueError("convergence evidence does not bind explicit p_min")


def validate_calculation_result(
    result: dict[str, Any], guardrail: dict[str, Any]
) -> None:
    _require_exact_keys(
        result,
        {
            "schema_id",
            "calculation_id",
            "calculation_status",
            "captured_at_utc",
            "guardrail",
            "question",
            "background_geometry_classification",
            "spacetime_dimension",
            "background_geometry",
            "mathematical_convention",
            "analytic_profile_references",
            "parameters",
            "method",
            "geometry_safety_verification",
            "geometry_verification",
            "profile_time_resolution_row_count",
            "profile_time_resolution_rows",
            "profile_resolution_aggregate_count",
            "profile_resolution_aggregates",
            "convergence_diagnostics",
            "flat_limit_control",
            "negative_controls",
            "thresholds",
            "threshold_evidence",
            "threshold_checks",
            "threshold_decisions",
            "frozen_threshold_count",
            "all_thresholds_passed",
            "selected_next_target",
            "claim",
            "existing_equation_id_reused",
            "equation_compendium_edited",
            "boundary",
            "result_review",
        },
        "calculation result",
    )
    if (
        result["schema_id"] != CALCULATION_RESULT_SCHEMA_ID
        or result["calculation_id"] != CALCULATION_ID
        or result["captured_at_utc"] != CAPTURED_AT_UTC
        or result["guardrail"]
        != {
            "path": str(GUARDRAIL_REPORT_PATH.relative_to(REPO_ROOT)).replace(
                "\\", "/"
            ),
            "sha256": EXPECTED_GUARDRAIL_SHA256,
            "schema_id": PACKET_SCHEMA_ID,
            "revised_at_utc": REVISED_AT_UTC,
        }
    ):
        raise ValueError("calculation result identity or guardrail link differs")
    if result["thresholds"] != _expected_execution_thresholds():
        raise ValueError("calculation thresholds differ from guardrail v1")
    if result["thresholds"] != guardrail["success_criteria"]:
        raise ValueError("calculation thresholds do not match loaded guardrail")
    _validate_result_rows(result)
    _validate_curvature_zero_reporting(result)
    _validate_negative_controls(result)
    _validate_convergence_diagnostics(result)

    flat = result["flat_limit_control"]
    if (
        flat["maximum_flat_limit_absolute_discrepancy"] > 1e-11
        or flat["operator_metadata"]
        != {
            "coordinate_order": ["t", "x", "y"],
            "operator_coefficients": [-1, 1, 1],
            "connection": 0,
            "curvature": 0,
            "symbolic_metadata_exact": True,
        }
        or len(flat["rows"]) != 36
    ):
        raise ValueError("flat-limit control differs from the frozen contract")

    checks = result["threshold_checks"]
    recomputed_checks = _recompute_execution_threshold_checks(result)
    if (
        set(checks) != THRESHOLD_IDS
        or len(checks) != 16
        or result["frozen_threshold_count"] != 16
        or checks != recomputed_checks
    ):
        raise ValueError("the exact sixteen threshold decisions differ")
    decisions = result["threshold_decisions"]
    if len(decisions) != 16:
        raise ValueError("the exact sixteen threshold decision rows differ")
    for frozen, observed in zip(FROZEN_THRESHOLD_DECISIONS, decisions):
        if any(observed.get(key) != value for key, value in frozen.items()):
            raise ValueError("threshold decision metadata differs")
        if observed.get("pass") is not checks[frozen["threshold_id"]]:
            raise ValueError("threshold decision pass flag differs")

    passed = all(checks.values())
    expected_target = REVIEW_TARGET if passed else DIAGNOSTIC_FAILURE_TARGET
    expected_status = (
        "executed_pending_result_review" if passed else "executed_blocked"
    )
    expected_label = "E-REPRO" if passed else "B-BLOCKED"
    expected_claim_status = (
        "generated_pending_result_review"
        if passed
        else "blocked_threshold_failure"
    )
    expected_result_review = (
        {"status": "pending", "target": REVIEW_TARGET}
        if passed
        else {"status": "not_created_threshold_failure", "target": None}
    )
    if (
        result["all_thresholds_passed"] is not passed
        or result["calculation_status"] != expected_status
        or result["selected_next_target"] != expected_target
        or result["claim"]["primary_label"] != expected_label
        or result["claim"]["claim_status"] != expected_claim_status
        or result["claim"]["claim_ceiling_level"] != 3
        or result["claim"]["next_work_status"] != expected_target
        or result["result_review"] != expected_result_review
    ):
        raise ValueError("execution lifecycle does not match threshold outcome")

    boundary = result["boundary"]
    required_true = {
        "calculation_executed",
        "two_dimensional_Einstein_degeneracy_not_applicable",
        "einstein_tensor_can_be_nonzero",
        "background_fixed",
    }
    required_false = {
        "gravity_evolved",
        "background_metric_evolved",
        "einstein_equation_solved",
        "Einstein_source_tested",
        "source_admissibility_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_seam_admissibility_claimed",
        "qft_gr_seam_closure_claimed",
        "quantum_or_renormalized_stress_energy_claimed",
        "multi_background_robustness_claimed",
        "level_4_or_level_5_claimed",
        "ccft_resumed",
        "master_action_promoted",
    }
    if (
        boundary.get("spacetime_dimension") != 3
        or not all(boundary.get(key) is True for key in required_true)
        or not all(boundary.get(key) is False for key in required_false)
        or "two_dimensional_einstein_gravity_degenerate"
        in json.dumps(result)
        or result["spacetime_dimension"] != 3
        or result["background_geometry_classification"]
        != BACKGROUND_GEOMETRY_CLASSIFICATION
        or result["existing_equation_id_reused"] != EQUATION_ID
        or result["equation_compendium_edited"] is not False
    ):
        raise ValueError("execution boundary or nonclaim metadata differs")
    canonical_json_bytes(result)


def validate_calculation_manifest(
    manifest: dict[str, Any],
    *,
    result: dict[str, Any],
    output_sha256: str,
    script_sha256: str,
) -> None:
    _require_exact_keys(
        manifest,
        {
            "schema_id",
            "calculation_id",
            "captured_at_utc",
            "guardrail_path",
            "guardrail_schema_id",
            "guardrail_sha256",
            "script_path",
            "script_sha256",
            "test_path",
            "execution_command",
            "environment",
            "output_path",
            "output_sha256",
            "execution_report_path",
            "canonical_json_contract",
            "temporary_output_paths_serialized",
            "wall_clock_timestamp_serialized",
            "background_geometry_classification",
            "spacetime_dimension",
            "claim_label",
            "claim_scope",
            "claim_ceiling_level",
            "all_thresholds_passed",
            "result_review_status",
            "result_review_target",
            "selected_next_target",
            "boundary",
        },
        "calculation manifest",
    )
    expected_contract = {
        "encoding": "UTF-8 without BOM",
        "newline": "LF",
        "object_keys": "sorted",
        "separators": [",", ":"],
        "ensure_ascii": True,
        "allow_nan": False,
        "array_order": "preserved",
        "trailing_newline": "exactly one LF",
    }
    if (
        manifest["schema_id"] != CALCULATION_MANIFEST_SCHEMA_ID
        or manifest["calculation_id"] != CALCULATION_ID
        or manifest["captured_at_utc"] != CAPTURED_AT_UTC
        or manifest["guardrail_path"]
        != str(GUARDRAIL_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
        or manifest["guardrail_schema_id"] != PACKET_SCHEMA_ID
        or manifest["guardrail_sha256"] != EXPECTED_GUARDRAIL_SHA256
        or manifest["script_path"] != CALCULATION_SCRIPT_RELATIVE_PATH
        or manifest["script_sha256"] != script_sha256
        or manifest["execution_command"] != CALCULATION_EXECUTION_COMMAND
        or manifest["output_path"] != CALCULATION_OUTPUT_RELATIVE_PATH
        or manifest["output_sha256"] != output_sha256
        or manifest["execution_report_path"] != EXECUTION_REPORT_RELATIVE_PATH
        or manifest["canonical_json_contract"] != expected_contract
        or manifest["temporary_output_paths_serialized"] is not False
        or manifest["wall_clock_timestamp_serialized"] is not False
        or manifest["background_geometry_classification"]
        != BACKGROUND_GEOMETRY_CLASSIFICATION
        or manifest["spacetime_dimension"] != 3
        or manifest["claim_label"] != result["claim"]["primary_label"]
        or manifest["claim_scope"] != result["claim"]["claim_scope"]
        or manifest["claim_ceiling_level"] != 3
        or manifest["all_thresholds_passed"]
        is not result["all_thresholds_passed"]
        or manifest["result_review_status"]
        != result["result_review"]["status"]
        or manifest["result_review_target"]
        != result["result_review"]["target"]
        or manifest["selected_next_target"] != result["selected_next_target"]
        or manifest["boundary"] != result["boundary"]
    ):
        raise ValueError("calculation manifest binding or lifecycle differs")
    environment = manifest["environment"]
    if set(environment) != {
        "python_version",
        "numpy_version",
        "operating_system_family",
        "machine_architecture",
        "endianness",
        "blas_lapack",
    } or environment["endianness"] not in {"little", "big"}:
        raise ValueError("stable environment metadata fields differ")
    if set(environment["blas_lapack"]) != {"blas", "lapack"}:
        raise ValueError("BLAS/LAPACK metadata fields differ")
    for dependency in environment["blas_lapack"].values():
        if set(dependency) != {"name", "version"} or not all(
            isinstance(value, str) for value in dependency.values()
        ):
            raise ValueError("BLAS/LAPACK metadata is not sanitized")
    canonical_json_bytes(manifest)


def build_execution_report(
    *,
    output_path: Path = CALCULATION_OUTPUT_PATH,
    manifest_path: Path = CALCULATION_MANIFEST_PATH,
    guardrail_path: Path = GUARDRAIL_REPORT_PATH,
    script_path: Path = CALCULATION_SCRIPT_PATH,
) -> dict[str, Any]:
    guardrail = _load_strict_json_object(guardrail_path)
    result = _load_strict_json_object(output_path)
    manifest = _load_strict_json_object(manifest_path)
    if guardrail_path.read_bytes() != report_json_bytes(guardrail):
        raise ValueError("guardrail is not canonical sorted report JSON")
    if output_path.read_bytes() != canonical_json_bytes(result):
        raise ValueError("calculation output is not canonical compact JSON")
    if manifest_path.read_bytes() != canonical_json_bytes(manifest):
        raise ValueError("calculation manifest is not canonical compact JSON")
    if sha256_path(guardrail_path) != EXPECTED_GUARDRAIL_SHA256:
        raise ValueError("accepted guardrail bytes changed")
    validate_guardrail_payload(guardrail)
    output_sha256 = sha256_path(output_path)
    manifest_sha256 = sha256_path(manifest_path)
    script_sha256 = sha256_path(script_path)
    validate_calculation_result(result, guardrail)
    validate_calculation_manifest(
        manifest,
        result=result,
        output_sha256=output_sha256,
        script_sha256=script_sha256,
    )

    passed = result["all_thresholds_passed"]
    selected_target = REVIEW_TARGET if passed else DIAGNOSTIC_FAILURE_TARGET
    return {
        "schema_id": EXECUTION_REPORT_SCHEMA_ID,
        "report_id": EXECUTION_REPORT_ID,
        "calculation_id": CALCULATION_ID,
        "status": (
            "executed_candidate_e_repro_pending_independent_review"
            if passed
            else "executed_blocked_threshold_failure"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "guardrail_revised_at_utc": REVISED_AT_UTC,
        "consumed_target": EXECUTION_TARGET,
        "consumed_target_kind": EXECUTION_TARGET_KIND,
        "selected_next_target": selected_target,
        "selected_next_target_kind": (
            REVIEW_TARGET_KIND if passed else "scientific_threshold_failure_diagnosis"
        ),
        "packet_result": (
            EXECUTION_OUTCOME if passed else EXECUTION_BLOCKED_OUTCOME
        ),
        "strict_packet_result": (
            EXECUTION_STRICT_OUTCOME
            if passed
            else EXECUTION_BLOCKED_STRICT_OUTCOME
        ),
        "guardrail_path": manifest["guardrail_path"],
        "guardrail_sha256": EXPECTED_GUARDRAIL_SHA256,
        "calculation_script_path": manifest["script_path"],
        "calculation_script_sha256": script_sha256,
        "calculation_output_path": manifest["output_path"],
        "calculation_output_sha256": output_sha256,
        "calculation_manifest_path": CALCULATION_MANIFEST_RELATIVE_PATH,
        "calculation_manifest_sha256": manifest_sha256,
        "execution_report_path": EXECUTION_REPORT_RELATIVE_PATH,
        "five_artifact_chain_prepared_for_independent_review": passed,
        "canonical_json_contract": manifest["canonical_json_contract"],
        "execution_command": manifest["execution_command"],
        "environment": manifest["environment"],
        "background_geometry_classification": (
            BACKGROUND_GEOMETRY_CLASSIFICATION
        ),
        "spacetime_dimension": 3,
        "control_counts": {
            "profile_count": 3,
            "time_slice_count": 3,
            "resolution_count": 4,
            "divergence_component_count": 3,
            "profile_time_resolution_row_count": 36,
            "profile_resolution_aggregate_count": 12,
            "curvature_route_count": 2,
            "flat_limit_row_count": 36,
            "negative_control_type_count": 5,
            "negative_control_record_count": 20,
            "frozen_threshold_decision_count": 16,
        },
        "geometry_safety_verification": result[
            "geometry_safety_verification"
        ],
        "geometry_verification": result["geometry_verification"],
        "convergence_diagnostics": result["convergence_diagnostics"],
        "flat_limit_control": result["flat_limit_control"],
        "negative_controls": result["negative_controls"],
        "thresholds": result["thresholds"],
        "threshold_evidence": result["threshold_evidence"],
        "threshold_checks": result["threshold_checks"],
        "threshold_decisions": result["threshold_decisions"],
        "all_thresholds_passed": passed,
        "claim": {
            "primary_label": "E-REPRO" if passed else "B-BLOCKED",
            "claim_status": (
                "candidate_pending_independent_result_review"
                if passed
                else "blocked_threshold_failure"
            ),
            "claim_ceiling_level": 3,
            "claim_scope": result["claim"]["claim_scope"],
            "review_accepted": False,
            "equation_surface_upgraded": False,
        },
        "existing_equation_id_reused": EQUATION_ID,
        "equation_compendium_edited": False,
        "boundary": result["boundary"],
        "full_ToeFormal_aggregate_run_or_upgraded": False,
        "ccft_lane_status": "paused_upstream_prerequisites",
        "lean_status_wording": (
            "scoped Lean pending execution certificate; full ToeFormal "
            "aggregate not run / not upgraded"
        ),
    }


def execution_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Report the fixed 2+1 warped-background scalar identity execution."
        )
    )
    parser.add_argument("--output", type=Path, default=CALCULATION_OUTPUT_PATH)
    parser.add_argument(
        "--manifest", type=Path, default=CALCULATION_MANIFEST_PATH
    )
    parser.add_argument("--guardrail", type=Path, default=GUARDRAIL_REPORT_PATH)
    parser.add_argument("--script", type=Path, default=CALCULATION_SCRIPT_PATH)
    parser.add_argument("--out", type=Path, default=EXECUTION_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_execution_report(
        output_path=args.output,
        manifest_path=args.manifest,
        guardrail_path=args.guardrail,
        script_path=args.script,
    )
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "all_thresholds_passed": payload["all_thresholds_passed"],
                "claim_label": payload["claim"]["primary_label"],
                "outcome": payload["packet_result"],
                "selected_next_target": payload["selected_next_target"],
                "execution_report": EXECUTION_REPORT_RELATIVE_PATH,
            },
            sort_keys=True,
        )
    )
    return 0 if payload["all_thresholds_passed"] else 1
