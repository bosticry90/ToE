from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.toe.calculations.calc_scalar_stress_energy_covariant_divergence_identity_nonzero_curvature_background import (
    RESOLUTIONS,
    TIME_SLICES,
    build_result as rebuild_calculation_result,
    canonical_json_bytes as calculation_canonical_json_bytes,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"

GUARDRAIL_TARGET = (
    "prepare_scalar_stress_energy_covariant_divergence_identity_nonzero_"
    "curvature_background_guardrail_packet"
)
EXECUTION_TARGET = (
    "execute_calc_scalar_stress_energy_covariant_divergence_identity_"
    "nonzero_curvature_background_v0"
)
EXECUTION_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_nonzero_curvature_"
    "background_calculation_execution"
)
REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_nonzero_"
    "curvature_background_v0_result"
)
REVIEW_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_nonzero_curvature_"
    "background_calculation_result_review"
)
THRESHOLD_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_covariant_divergence_identity_nonzero_"
    "curvature_background_v0_threshold_failure"
)
REPRODUCIBILITY_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_covariant_divergence_identity_nonzero_"
    "curvature_background_v0_reproducibility_mismatch"
)
HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_TARGET = (
    "prepare_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_guardrail_packet"
)

GUARDRAIL_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_CURVATURE_"
    "BACKGROUND_GUARDRAIL_PACKET_PREPARED_AUTHORIZES_FIXED_DE_SITTER_PATCH_"
    "COVARIANT_DIVERGENCE_IDENTITY_CALCULATION_ONLY"
)
GUARDRAIL_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_CURVATURE_"
    "BACKGROUND_GUARDRAIL_PACKET_PREPARED_LEVEL_3_SINGLE_NONZERO_CURVATURE_"
    "BACKGROUND_TEST_ONLY_NO_GRAVITY_EVOLUTION_NO_SOURCE_ADMISSIBILITY_NO_"
    "BIANCHI_OR_SEAM_ADMISSIBILITY_NO_MASTER_ACTION_PROMOTION"
)
EXECUTION_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_CURVATURE_"
    "BACKGROUND_CALCULATION_EXECUTED_PASSES_LEVEL_3_FIXED_1PLUS1_DE_SITTER_"
    "CURVATURE_CONNECTION_AND_MATTER_IDENTITY_CONTROLS_PENDING_RESULT_REVIEW"
)
EXECUTION_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_CURVATURE_"
    "BACKGROUND_CALCULATION_EXECUTED_SCOPED_E_REPRO_PENDING_REVIEW_FIXED_"
    "1PLUS1_DE_SITTER_MATTER_IDENTITY_ONLY_TWO_DIMENSIONAL_EINSTEIN_GRAVITY_"
    "DEGENERATE_NO_EINSTEIN_SOURCE_TEST_NO_SOURCE_ADMISSIBILITY_NO_BIANCHI_"
    "OR_SEAM_ADMISSIBILITY_NO_MASTER_ACTION_PROMOTION"
)
REVIEW_OUTCOME = (
    "CALC_SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
    "CURVATURE_BACKGROUND_RESULT_REVIEW_ACCEPTS_REPRODUCIBLE_FIXED_1PLUS1_"
    "DE_SITTER_MATTER_IDENTITY_ONLY_NO_EINSTEIN_SOURCE_OR_SEAM_"
    "ADMISSIBILITY_CLAIM"
)
REVIEW_STRICT_OUTCOME = (
    "CALC_SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
    "CURVATURE_BACKGROUND_RESULT_REVIEW_ACCEPTS_LEVEL3_SCOPED_E_REPRO_ONLY_"
    "NO_BIANCHI_COMPATIBILITY_NO_QFT_GR_SEAM_CLOSURE_NO_MASTER_ACTION_"
    "PROMOTION"
)

PACKET_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_CURVATURE_"
    "BACKGROUND_GUARDRAIL_PACKET_20260709_v0"
)
PACKET_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_CURVATURE_"
    "BACKGROUND_GUARDRAIL_PACKET_v0"
)
CALCULATION_ID = (
    "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-NONZERO-"
    "CURVATURE-BACKGROUND-v0"
)
EQUATION_ID = "EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0"

GUARDRAIL_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
    "CURVATURE_BACKGROUND_GUARDRAIL_PACKET_20260709_v0.json"
)
PREDECESSOR_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_"
    "BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0.json"
)
READINESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
CALCULATION_OUTPUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-NONZERO-"
    "CURVATURE-BACKGROUND-v0.json"
)
CALCULATION_MANIFEST_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-NONZERO-"
    "CURVATURE-BACKGROUND-MANIFEST-v0.json"
)
CALCULATION_SCRIPT_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "toe"
    / "calculations"
    / "calc_scalar_stress_energy_covariant_divergence_identity_nonzero_"
    "curvature_background.py"
)
EXECUTION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
    "CURVATURE_BACKGROUND_CALCULATION_EXECUTION_20260709_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
    "CURVATURE_BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0.json"
)

BACKGROUND_GEOMETRY_CLASSIFICATION = (
    "fixed_nonzero_curvature_1plus1_de_sitter_patch"
)
GUARDRAIL_GEOMETRY_CLASSIFICATION = (
    "fixed_1_plus_1_de_sitter_conformal_patch"
)
EXPECTED_GUARDRAIL_SHA256 = (
    "3670bfaa98876b32e95f5ff7406546a41aa691f937fe738fee6e3ab36a399191"
)
EXPECTED_EXECUTION_HASHES = {
    "guardrail_sha256": EXPECTED_GUARDRAIL_SHA256,
    "script_sha256": (
        "253632cc6773d242a76db26befde13dc2578a2950c097a8c628b8e061ffdbd03"
    ),
    "output_sha256": (
        "4d0d04421c8b0d310f0caa73c4da3755f2afa91a4043bab9f96011c9b03ecf4f"
    ),
    "manifest_sha256": (
        "46e752fd0a8571fd06dd0f1f9a7046f12a43413761ea39a3cb904b959a4a6827"
    ),
    "execution_report_sha256": (
        "21068eaff2b509401afb635e4f7bce4eb409edb8a5cff6dfe4bea7dfe7a3d2c8"
    ),
}


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


def build_guardrail_payload() -> dict[str, Any]:
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "prepared_authorizes_execution_only",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": GUARDRAIL_TARGET,
        "consumed_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_nonzero_"
            "curvature_background_guardrail_packet"
        ),
        "selected_next_target": EXECUTION_TARGET,
        "selected_next_target_kind": EXECUTION_TARGET_KIND,
        "packet_result": GUARDRAIL_OUTCOME,
        "strict_packet_result": GUARDRAIL_STRICT_OUTCOME,
        "accepted_predecessor": {
            "artifact_id": (
                "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
                "CONFORMAL_BACKGROUND_CALCULATION_RESULT_REVIEW_v0"
            ),
            "path": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_"
                "DIVERGENCE_IDENTITY_CONFORMAL_BACKGROUND_CALCULATION_"
                "RESULT_REVIEW_20260709_v0.json"
            ),
            "sha256": sha256_path(PREDECESSOR_REVIEW_PATH),
            "accepted_claim_ceiling": "Level 3 toy-model demonstration",
            "accepted_scope": (
                "locally flat nontrivial conformal connection identity test"
            ),
        },
        "readiness_authority": {
            "artifact_id": "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0",
            "path": "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json",
            "sha256": sha256_path(READINESS_PATH),
            "status": "accepted_current_science_sprint_readiness_authority",
        },
        "question": (
            "Does the scalar covariant stress-energy divergence identity hold "
            "numerically for exact source-free on-shell and deliberately "
            "off-shell controls on one fixed genuinely curved de Sitter "
            "conformal patch?"
        ),
        "inputs": {
            "coordinates": ["eta", "x"],
            "dimension": 2,
            "coordinate_domain": {
                "eta": "eta in [0,1]",
                "x": "x in [0,2*pi), periodic",
            },
            "time_slices_eta": [0.0, 0.37, 0.91],
            "spatial_resolutions_N": [64, 128, 256, 512],
            "conformal_hubble_parameter_H": 0.2,
            "scale_factor": "a(eta) = (1 - H*eta)^(-1)",
            "logarithmic_scale_derivative": (
                "q(eta) = a'(eta)/a(eta) = H/(1-H*eta)"
            ),
            "field": "phi(eta,x) = A cos(k*x - omega*eta)",
            "amplitude_A": 0.2,
            "wave_number_k": 2.0,
            "mass_m": 0.0,
            "omega_on": 2.0,
            "omega_off": 2.2,
            "off_shell_exact_coefficient": 0.84,
            "off_shell_exact_residual": "E_phi = 0.84 * a(eta)^(-2) * phi",
        },
        "background_geometry": {
            "classification": "fixed_1_plus_1_de_sitter_conformal_patch",
            "metric": "g_mu_nu = a(eta)^2 * diag(-1,+1)",
            "inverse_metric": "g^mu_nu = a(eta)^(-2) * diag(-1,+1)",
            "metric_signature": "(-,+)",
            "volume_density": "sqrt(-g) = a(eta)^2",
            "analytic_scalar_curvature": "R = 2*H^2 = 0.08",
            "scalar_curvature": 0.08,
            "genuinely_nonzero_curvature_required": True,
            "fixed_background_only": True,
            "gravity_evolved": False,
        },
        "equation_surfaces": {
            "scalar_action": (
                "S[phi,g] = integral d^2x sqrt(-g) [-1/2 g^{mu nu} "
                "partial_mu phi partial_nu phi - V(phi)] with V(phi)=0"
            ),
            "stress_energy": (
                "T^{mu nu} = nabla^mu phi nabla^nu phi - g^{mu nu} "
                "[1/2 nabla_alpha phi nabla^alpha phi + V(phi)]"
            ),
            "field_residual": "E_phi = Box_g phi - V'(phi) = Box_g phi",
            "covariant_dalembertian": (
                "Box_g phi = 1/sqrt(-g) partial_mu [sqrt(-g) g^{mu nu} "
                "partial_nu phi] = a(eta)^(-2)(-partial_eta^2 + "
                "partial_x^2) phi"
            ),
            "covariant_divergence": (
                "nabla_mu T^{mu nu} = partial_mu T^{mu nu} + "
                "Gamma^mu_{mu lambda} T^{lambda nu} + "
                "Gamma^nu_{mu lambda} T^{mu lambda}"
            ),
            "identity": "nabla_mu T^{mu nu} = E_phi nabla^nu phi",
            "existing_equation_id_reused": EQUATION_ID,
            "existing_equation_status": "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO",
            "equation_surface_upgraded": False,
            "equation_compendium_edited": False,
        },
        "connection_and_curvature_conventions": {
            "christoffel_definition": (
                "Gamma^rho_{mu nu} = 1/2 g^{rho sigma} "
                "(partial_mu g_{sigma nu} + partial_nu g_{sigma mu} - "
                "partial_sigma g_{mu nu})"
            ),
            "nonzero_christoffels": {
                "Gamma^eta_{eta eta}": "q(eta)",
                "Gamma^eta_{x x}": "q(eta)",
                "Gamma^x_{eta x}": "q(eta)",
                "Gamma^x_{x eta}": "q(eta)",
            },
            "riemann_sign": (
                "R^rho_{sigma mu nu} = partial_mu Gamma^rho_{nu sigma} - "
                "partial_nu Gamma^rho_{mu sigma} + "
                "Gamma^rho_{mu lambda} Gamma^lambda_{nu sigma} - "
                "Gamma^rho_{nu lambda} Gamma^lambda_{mu sigma}"
            ),
            "ricci_contraction": "R_{sigma nu} = R^rho_{sigma rho nu}",
            "scalar_contraction": "R = g^{sigma nu} R_{sigma nu}",
        },
        "curvature_verification": {
            "analytic_conformal_route": {
                "formula": (
                    "R_analytic = 2*a(eta)^(-2)*partial_eta q(eta) "
                    "= 2*H^2"
                ),
                "expected_value": 0.08,
            },
            "independent_component_route": {
                "route": [
                    "metric",
                    "inverse_metric",
                    "metric_derivatives",
                    "Christoffel_symbols",
                    "Riemann_tensor",
                    "Ricci_tensor",
                    "scalar_contraction",
                ],
                "formula_shortcut_prohibited": (
                    "do not use the analytic conformal scalar-curvature formula"
                ),
                "expected_ricci_relation": "R_mu_nu = H^2 * g_mu_nu",
                "expected_value": 0.08,
                "evaluation_points": "all frozen time slices",
            },
            "maximum_route_agreement_absolute_error": 1e-12,
            "minimum_absolute_scalar_curvature": 0.05,
        },
        "solution_controls": {
            "on_shell_positive_control": {
                "omega": 2.0,
                "classification": "exact_source_free_solution",
                "forced_or_manufactured": False,
                "exact_residual": "E_phi = 0",
            },
            "off_shell_control": {
                "omega": 2.2,
                "classification": "deliberately_off_shell_unforced_field",
                "forced_or_manufactured": False,
                "exact_residual": "E_phi = 0.84 * a(eta)^(-2) * phi",
            },
        },
        "negative_controls": {
            "naive_partial_divergence": {
                "operation": "omit all connection terms from nabla_mu T^{mu nu}",
                "ratio_definition": (
                    "space-time combined RMS naive identity error divided by "
                    "the correct covariant identity error"
                ),
                "minimum_error_ratio": 100.0,
            },
            "curvature_derivative_omission": {
                "operation": (
                    "omit derivative-of-Gamma terms in the curvature "
                    "reconstruction"
                ),
                "expected_bad_scalar_curvature": 0.0,
                "minimum_absolute_discrepancy_from_reference": 0.04,
            },
            "inconsistent_frozen_connection": {
                "operation": (
                    "replace q(eta) by the constant H in the divergence identity"
                ),
                "ratio_definition": (
                    "space-time combined RMS inconsistent-connection identity "
                    "error divided by the correct covariant identity error"
                ),
                "minimum_error_ratio": 50.0,
            },
        },
        "assumptions": [
            "fixed prescribed 1+1-dimensional de Sitter conformal patch",
            "real massless minimally coupled scalar with V(phi)=0",
            "exact source-free plane-wave on-shell solution; no manufactured forcing",
            "periodic spatial boundary",
            "analytic metric, connection, field, and temporal derivatives",
            "second-order numerical spatial derivatives",
            "no metric evolution and no Einstein-equation solve",
        ],
        "units": {
            "convention": "dimensionless numerical test units with c = hbar = 1",
            "coordinate_parameter_consistency": (
                "eta, x, H, k, and omega use one natural-unit normalization"
            ),
            "physical_parameter_inference_allowed": False,
        },
        "numerical_method": {
            "temporal_derivatives": "analytic",
            "metric_and_connection_derivatives": "analytic",
            "spatial_derivatives": "second-order centered periodic finite differences",
            "component_rms_norm_at_each_time": "sqrt(mean_x(v_nu^2))",
            "combined_rms_norm_at_each_time": "sqrt(mean_x(v_eta^2 + v_x^2))",
            "space_time_combined_rms_norm": (
                "sqrt(mean_{eta,x}(v_eta^2 + v_x^2)) over frozen time slices"
            ),
            "off_shell_identity_relative_error": (
                "norm(nabla_mu T^{mu nu} - E_phi nabla^nu phi) / "
                "max(norm(E_phi nabla^nu phi),1e-14)"
            ),
            "on_shell_error_policy": (
                "report absolute covariant-divergence norms; no relative error "
                "against a zero reference"
            ),
            "convergence_order": "log2(error_N/error_2N) over two finest pairs",
            "flat_limit_comparison": (
                "set H=0 and compare with the accepted Cartesian Minkowski "
                "implementation"
            ),
        },
        "allowed_operations": [
            "evaluate the prescribed metric, inverse metric, and connection",
            "evaluate analytic scalar and temporal derivatives",
            "apply second-order centered periodic spatial differences",
            "compute both nu=eta and nu=x covariant divergence components",
            "reconstruct curvature independently from metric components",
            "check metric compatibility nabla_lambda g_mu_nu = 0",
            "check H=0 flat-limit recovery against the Minkowski implementation",
            "run the three frozen negative controls",
            "compute component, combined, and space-time RMS norms",
            "estimate convergence orders over the two finest refinement pairs",
            "write deterministic result, manifest, and execution report artifacts",
        ],
        "forbidden_claims": [
            "general curved-spacetime theorem",
            "dynamical gravity or Einstein-equation solution",
            "GR source admissibility",
            "Bianchi compatibility discharge",
            "QFT-GR seam admissibility or closure",
            "quantum or renormalized stress-energy source",
            "pillar completion",
            "CCFT validation or resumption",
            "master-action canonicalization, promotion, or closure",
        ],
        "required_controls": {
            "analytic_curvature_route": True,
            "independent_component_curvature_route": True,
            "curvature_route_agreement": True,
            "nonzero_curvature_floor": True,
            "metric_compatibility": True,
            "flat_limit_recovery": True,
            "on_shell_positive_control": True,
            "off_shell_control": True,
            "naive_partial_divergence_negative_control": True,
            "curvature_derivative_omission_negative_control": True,
            "inconsistent_frozen_connection_negative_control": True,
            "grid_refinement": True,
            "deterministic_reexecution": True,
            "complete_hash_manifest": True,
        },
        "success_criteria": {
            "minimum_convergence_order_two_finest_pairs": 1.8,
            "maximum_finest_combined_off_shell_relative_error": 0.02,
            "maximum_exact_coefficient_absolute_error": 1e-12,
            "minimum_finest_off_to_on_divergence_norm_ratio": 100.0,
            "maximum_metric_compatibility_absolute_error": 1e-12,
            "maximum_flat_limit_absolute_discrepancy": 1e-12,
            "maximum_curvature_route_absolute_discrepancy": 1e-12,
            "minimum_absolute_scalar_curvature": 0.05,
            "minimum_naive_partial_divergence_identity_error_ratio": 100.0,
            "minimum_curvature_omission_absolute_discrepancy": 0.04,
            "minimum_inconsistent_frozen_connection_identity_error_ratio": 50.0,
            "all_thresholds_required": True,
        },
        "failure_criteria": {
            "any_threshold_failure": True,
            "primary_claim_label": "B-BLOCKED",
            "selected_repair_target": THRESHOLD_REPAIR_TARGET,
            "failed_artifacts_preserved": True,
            "threshold_changes_require_new_versioned_guardrail": True,
        },
        "outputs": {
            "result": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-"
                "DIVERGENCE-IDENTITY-NONZERO-CURVATURE-BACKGROUND-v0.json"
            ),
            "manifest": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-"
                "DIVERGENCE-IDENTITY-NONZERO-CURVATURE-BACKGROUND-"
                "MANIFEST-v0.json"
            ),
            "execution_report": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_"
                "DIVERGENCE_IDENTITY_NONZERO_CURVATURE_BACKGROUND_"
                "CALCULATION_EXECUTION_20260709_v0.json"
            ),
        },
        "claim_ceiling": {
            "claim_ladder_level": 3,
            "classification": "single_fixed_nonzero_curvature_background_test",
            "execution_e_repro_status": "pending_result_review",
            "not_general_curved_spacetime_theorem": True,
            "not_gravity_dynamics": True,
            "not_source_admissibility": True,
            "not_bianchi_compatibility": True,
            "not_seam_admissibility": True,
        },
        "reproduction_command": (
            "python -m formal.python.toe.calculations."
            "calc_scalar_stress_energy_covariant_divergence_identity_"
            "nonzero_curvature_background"
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
        "calculation_id": CALCULATION_ID,
        "calculation_executed": False,
        "e_repro_claimed": False,
        "equation_compendium_row_added": False,
        "ccft_lane_status": "paused_upstream_prerequisites",
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def validate_guardrail_payload(payload: dict[str, Any]) -> None:
    required_interface = {
        "question",
        "inputs",
        "background_geometry",
        "equation_surfaces",
        "connection_and_curvature_conventions",
        "curvature_verification",
        "solution_controls",
        "negative_controls",
        "assumptions",
        "units",
        "allowed_operations",
        "forbidden_claims",
        "required_controls",
        "success_criteria",
        "failure_criteria",
        "outputs",
        "claim_ceiling",
        "reproduction_command",
    }
    if not required_interface.issubset(payload):
        raise ValueError("guardrail is missing required sprint interface fields")
    if payload.get("schema_id") != PACKET_SCHEMA_ID:
        raise ValueError("guardrail schema id differs")
    if payload.get("consumed_target") != GUARDRAIL_TARGET:
        raise ValueError("guardrail does not consume the live preparation target")
    if payload.get("selected_next_target") != EXECUTION_TARGET:
        raise ValueError("guardrail does not select the bounded execution target")
    if payload["claim_ceiling"].get("claim_ladder_level") != 3:
        raise ValueError("claim ceiling must remain Level 3")
    if payload["background_geometry"].get("scalar_curvature") != 0.08:
        raise ValueError("scalar curvature differs from the frozen value")
    if payload["inputs"].get("off_shell_exact_coefficient") != 0.84:
        raise ValueError("off-shell coefficient differs from the frozen value")
    if payload["solution_controls"]["on_shell_positive_control"].get(
        "forced_or_manufactured"
    ) is not False:
        raise ValueError("on-shell control must remain source-free and unforced")
    if not all(payload["required_controls"].values()):
        raise ValueError("all frozen controls are required")
    if payload["equation_surfaces"].get("equation_surface_upgraded") is not False:
        raise ValueError("guardrail cannot upgrade the accepted equation surface")
    if payload.get("calculation_executed") is not False:
        raise ValueError("guardrail cannot claim calculation execution")
    canonical_json_bytes(payload)


def _reject_nonfinite_json(token: str) -> None:
    raise ValueError(f"non-finite JSON token: {token}")


def _load_strict_json(path: Path) -> dict[str, Any]:
    payload = json.loads(
        path.read_text(encoding="utf-8"),
        parse_constant=_reject_nonfinite_json,
    )
    if not isinstance(payload, dict):
        raise ValueError(f"expected a JSON object at {path}")
    canonical_json_bytes(payload)
    return payload


def build_execution_report(
    *,
    output_path: Path = CALCULATION_OUTPUT_PATH,
    manifest_path: Path = CALCULATION_MANIFEST_PATH,
    guardrail_path: Path = GUARDRAIL_REPORT_PATH,
    script_path: Path = CALCULATION_SCRIPT_PATH,
) -> dict[str, Any]:
    result = _load_strict_json(output_path)
    manifest = _load_strict_json(manifest_path)
    guardrail = _load_strict_json(guardrail_path)

    if output_path.read_bytes() != canonical_json_bytes(result):
        raise ValueError("calculation output is not canonical JSON")
    if manifest_path.read_bytes() != canonical_json_bytes(manifest):
        raise ValueError("calculation manifest is not canonical JSON")

    output_sha256 = sha256_path(output_path)
    manifest_sha256 = sha256_path(manifest_path)
    guardrail_sha256 = sha256_path(guardrail_path)
    script_sha256 = sha256_path(script_path)
    if guardrail_sha256 != EXPECTED_GUARDRAIL_SHA256:
        raise ValueError("accepted guardrail bytes changed")
    if manifest.get("output_sha256") != output_sha256:
        raise ValueError("manifest output hash differs from the output bytes")
    if manifest.get("guardrail_sha256") != guardrail_sha256:
        raise ValueError("manifest guardrail hash differs from the accepted packet")
    if manifest.get("script_sha256") != script_sha256:
        raise ValueError("manifest script hash differs from the execution source")
    if manifest.get("calculation_id") != CALCULATION_ID:
        raise ValueError("manifest calculation id differs")
    if result.get("calculation_id") != CALCULATION_ID:
        raise ValueError("result calculation id differs")
    if result.get("calculation_status") != "executed_pending_result_review":
        raise ValueError("calculation is not in the pending-review state")
    if result.get("all_thresholds_passed") is not True:
        raise ValueError("calculation thresholds did not all pass")
    checks = result.get("threshold_checks", {})
    if len(checks) != 11 or not all(checks.values()):
        raise ValueError("the eleven frozen threshold checks were not preserved")
    if result.get("frozen_threshold_count") != 11:
        raise ValueError("frozen threshold count differs")
    if result.get("thresholds") != guardrail.get("success_criteria"):
        raise ValueError("execution thresholds differ from the accepted guardrail")

    if result.get("background_geometry_classification") != (
        BACKGROUND_GEOMETRY_CLASSIFICATION
    ):
        raise ValueError("execution geometry classification differs")
    background = result.get("background_geometry", {})
    if background.get("guardrail_geometry_classification") != (
        GUARDRAIL_GEOMETRY_CLASSIFICATION
    ):
        raise ValueError("guardrail geometry classification was not preserved")
    if result.get("scalar_curvature_expected") != 0.08:
        raise ValueError("expected scalar curvature differs")
    if result.get("scalar_curvature_measured") != 0.08:
        raise ValueError("measured scalar curvature differs")
    curvature = result.get("curvature_verification", {})
    if curvature.get("maximum_route_agreement_absolute_error", 1.0) > 1e-12:
        raise ValueError("curvature routes do not agree within tolerance")
    if curvature.get("minimum_absolute_measured_scalar_curvature", 0.0) < 0.05:
        raise ValueError("measured curvature does not clear the nonzero floor")
    if curvature.get("ricci_relation_max_absolute_error", 1.0) > 1e-12:
        raise ValueError("independent Ricci reconstruction differs")

    patch = result.get("patch_domain_safety", {})
    expected_patch_values = {
        "eta_domain": [0.0, 1.0],
        "coordinate_patch_singularity_eta": 5.0,
        "minimum_one_minus_H_eta_over_domain": 0.8,
        "maximum_scale_factor_over_domain": 1.25,
        "minimum_coordinate_distance_to_patch_singularity_over_domain": 4.0,
        "strictly_inside_coordinate_patch": True,
        "coordinate_patch_boundary_is_physical_curvature_singularity": False,
        "derived_invariant_not_additional_guardrail_threshold": True,
    }
    if any(patch.get(key) != value for key, value in expected_patch_values.items()):
        raise ValueError("coordinate-patch safety metadata differs")

    negative_controls = result.get("negative_controls", {})
    expected_negative_controls = {
        "naive_partial_divergence",
        "inconsistent_frozen_connection",
        "curvature_derivative_omission",
    }
    if set(negative_controls) != expected_negative_controls:
        raise ValueError("the three frozen negative controls were not preserved")
    if not all(
        negative_controls[name].get("failure_detected") is True
        for name in expected_negative_controls
    ):
        raise ValueError("one or more negative controls did not detect failure")

    boundary = result.get("boundary", {})
    required_true_boundary = {
        "calculation_executed",
        "two_dimensional_einstein_gravity_degenerate",
        "einstein_tensor_identically_zero_in_two_dimensions",
        "covariant_matter_identity_tested",
        "genuine_nonzero_curvature_test_executed",
        "curvature_test_claimed",
    }
    required_false_boundary = {
        "gravity_evolved",
        "background_metric_evolved",
        "einstein_equation_solved",
        "einstein_tensor_source_tested",
        "ordinary_einstein_scalar_dynamics_claimed",
        "source_admissibility_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_seam_admissibility_claimed",
        "qft_gr_seam_closure_claimed",
        "quantum_stress_energy_source_claimed",
        "multi_background_robustness_claimed",
        "higher_dimensional_robustness_claimed",
        "pillar_completion_claimed",
        "ccft_resumed",
        "ccft_validated",
        "master_action_promoted",
    }
    if not all(boundary.get(key) is True for key in required_true_boundary):
        raise ValueError("required execution boundary metadata is missing")
    if not all(boundary.get(key) is False for key in required_false_boundary):
        raise ValueError("a forbidden execution-boundary claim is present")
    if result.get("gravity_evolved") is not False:
        raise ValueError("top-level gravity-evolved metadata differs")
    if result.get("einstein_tensor_source_tested") is not False:
        raise ValueError("top-level Einstein-source metadata differs")
    if result.get("two_dimensional_einstein_gravity_degenerate") is not True:
        raise ValueError("two-dimensional Einstein degeneracy was not recorded")
    if result.get("covariant_matter_identity_tested") is not True:
        raise ValueError("covariant matter identity was not recorded")
    if result.get("equation_compendium_edited") is not False:
        raise ValueError("execution cannot edit the equation compendium")
    if result.get("claim", {}).get("next_work_status") != REVIEW_TARGET:
        raise ValueError("result does not select the separate review target")
    if result.get("result_review", {}).get("target") != REVIEW_TARGET:
        raise ValueError("result-review target differs")
    if manifest.get("result_review_target") != REVIEW_TARGET:
        raise ValueError("manifest result-review target differs")

    return {
        "schema_id": (
            "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
            "CURVATURE_BACKGROUND_CALCULATION_EXECUTION_20260709_v0"
        ),
        "calculation_id": CALCULATION_ID,
        "status": "executed_pending_result_review",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": EXECUTION_TARGET,
        "consumed_target_kind": EXECUTION_TARGET_KIND,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "packet_result": EXECUTION_OUTCOME,
        "strict_packet_result": EXECUTION_STRICT_OUTCOME,
        "calculation_output_path": manifest["output_path"],
        "calculation_output_sha256": output_sha256,
        "calculation_manifest_path": (
            "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
            "IDENTITY-NONZERO-CURVATURE-BACKGROUND-MANIFEST-v0.json"
        ),
        "calculation_manifest_sha256": manifest_sha256,
        "guardrail_path": manifest["guardrail_path"],
        "guardrail_sha256": guardrail_sha256,
        "calculation_script_path": manifest["script_path"],
        "calculation_script_sha256": script_sha256,
        "execution_report_path": (
            "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_"
            "IDENTITY_NONZERO_CURVATURE_BACKGROUND_CALCULATION_EXECUTION_"
            "20260709_v0.json"
        ),
        "canonical_json_contract": manifest["canonical_json_contract"],
        "background_geometry_classification": (
            BACKGROUND_GEOMETRY_CLASSIFICATION
        ),
        "guardrail_geometry_classification": GUARDRAIL_GEOMETRY_CLASSIFICATION,
        "scalar_curvature_expected": result["scalar_curvature_expected"],
        "scalar_curvature_measured": result["scalar_curvature_measured"],
        "curvature_verification": curvature,
        "patch_domain_safety": patch,
        "control_counts": {
            "curvature_verification_route_count": 2,
            "negative_control_count": 3,
            "frozen_threshold_count": 11,
            "on_shell_time_resolution_rows": len(
                result["on_shell"]["time_slice_results"]
            ),
            "off_shell_time_resolution_rows": len(
                result["off_shell"]["time_slice_results"]
            ),
            "time_slice_count": len(result["parameters"]["time_slices_eta"]),
            "resolution_count": len(result["parameters"]["resolutions_N"]),
            "divergence_component_count": 2,
        },
        "negative_controls": negative_controls,
        "threshold_evidence": result["threshold_evidence"],
        "threshold_checks": checks,
        "all_thresholds_passed": True,
        "claim": {
            "primary_label": "E-REPRO",
            "claim_status": "generated_pending_result_review",
            "claim_ceiling_level": 3,
            "claim_scope": result["claim"]["claim_scope"],
        },
        "gravity_evolved": False,
        "einstein_tensor_source_tested": False,
        "two_dimensional_einstein_gravity_degenerate": True,
        "covariant_matter_identity_tested": True,
        "existing_equation_id_reused": result["existing_equation_id_reused"],
        "equation_compendium_edited": False,
        "recommended_post_review_target": result[
            "recommended_post_review_target"
        ],
        "boundary": boundary,
        "ccft_lane_status": "paused_upstream_prerequisites",
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def _json_fragment_sha256(payload: Any) -> str:
    return sha256_bytes(calculation_canonical_json_bytes(payload))


def _recompute_threshold_checks(
    evidence: dict[str, Any], thresholds: dict[str, Any]
) -> dict[str, bool]:
    return {
        "two_finest_convergence_order_at_least_1_8": (
            evidence["minimum_observed_two_finest_convergence_order"]
            >= thresholds["minimum_convergence_order_two_finest_pairs"]
        ),
        "finest_combined_off_shell_relative_error_at_most_2_percent": (
            evidence["finest_combined_off_shell_relative_error"]
            <= thresholds["maximum_finest_combined_off_shell_relative_error"]
        ),
        "exact_coefficient_error_at_most_1e_12": (
            evidence["exact_coefficient_absolute_error"]
            <= thresholds["maximum_exact_coefficient_absolute_error"]
        ),
        "finest_off_shell_divergence_over_100_times_on_shell": (
            evidence["finest_off_to_on_divergence_norm_ratio"]
            >= thresholds["minimum_finest_off_to_on_divergence_norm_ratio"]
        ),
        "metric_compatibility_error_at_most_1e_12": (
            evidence["metric_compatibility_max_absolute_error"]
            <= thresholds["maximum_metric_compatibility_absolute_error"]
        ),
        "flat_limit_discrepancy_at_most_1e_12": (
            evidence["flat_limit_max_absolute_discrepancy"]
            <= thresholds["maximum_flat_limit_absolute_discrepancy"]
        ),
        "curvature_route_discrepancy_at_most_1e_12": (
            evidence["curvature_route_max_absolute_discrepancy"]
            <= thresholds["maximum_curvature_route_absolute_discrepancy"]
        ),
        "absolute_scalar_curvature_at_least_0_05": (
            evidence["minimum_absolute_measured_scalar_curvature"]
            >= thresholds["minimum_absolute_scalar_curvature"]
        ),
        "naive_partial_divergence_error_ratio_at_least_100": (
            evidence["finest_on_shell_naive_to_correct_error_ratio"]
            >= thresholds[
                "minimum_naive_partial_divergence_identity_error_ratio"
            ]
        ),
        "curvature_omission_discrepancy_at_least_0_04": (
            evidence["curvature_omission_minimum_absolute_discrepancy"]
            >= thresholds["minimum_curvature_omission_absolute_discrepancy"]
        ),
        "inconsistent_frozen_connection_error_ratio_at_least_50": (
            evidence[
                "finest_minimum_on_off_frozen_connection_to_correct_error_ratio"
            ]
            >= thresholds[
                "minimum_inconsistent_frozen_connection_identity_error_ratio"
            ]
        ),
    }


def verify_calculation_result(
    *,
    guardrail_path: Path = GUARDRAIL_REPORT_PATH,
    script_path: Path = CALCULATION_SCRIPT_PATH,
    output_path: Path = CALCULATION_OUTPUT_PATH,
    manifest_path: Path = CALCULATION_MANIFEST_PATH,
    execution_report_path: Path = EXECUTION_REPORT_PATH,
) -> dict[str, Any]:
    """Independently review the immutable nonzero-curvature execution."""

    mismatch_codes: list[str] = []
    actual_hashes = {
        "guardrail_sha256": sha256_path(guardrail_path),
        "script_sha256": sha256_path(script_path),
        "output_sha256": sha256_path(output_path),
        "manifest_sha256": sha256_path(manifest_path),
        "execution_report_sha256": sha256_path(execution_report_path),
    }
    hash_code_by_key = {
        "guardrail_sha256": "guardrail_hash_mismatch",
        "script_sha256": "script_hash_mismatch",
        "output_sha256": "output_hash_mismatch",
        "manifest_sha256": "manifest_hash_mismatch",
        "execution_report_sha256": "execution_report_hash_mismatch",
    }
    for key, expected in EXPECTED_EXECUTION_HASHES.items():
        if actual_hashes[key] != expected:
            mismatch_codes.append(hash_code_by_key[key])

    artifacts: dict[str, dict[str, Any] | None] = {
        "guardrail": None,
        "result": None,
        "manifest": None,
        "execution_report": None,
    }
    artifact_paths = {
        "guardrail": guardrail_path,
        "result": output_path,
        "manifest": manifest_path,
        "execution_report": execution_report_path,
    }
    for name, path in artifact_paths.items():
        try:
            artifacts[name] = _load_strict_json(path)
        except (UnicodeDecodeError, json.JSONDecodeError, ValueError):
            mismatch_codes.append("schema_mismatch")

    guardrail = artifacts["guardrail"]
    result = artifacts["result"]
    manifest = artifacts["manifest"]
    execution_report = artifacts["execution_report"]

    canonical_byte_checks = {
        "guardrail_report_bytes": False,
        "calculation_output_bytes": False,
        "calculation_manifest_bytes": False,
        "execution_report_bytes": False,
    }
    try:
        canonical_byte_checks["guardrail_report_bytes"] = (
            guardrail is not None
            and guardrail_path.read_bytes() == report_json_bytes(guardrail)
        )
        canonical_byte_checks["calculation_output_bytes"] = (
            result is not None
            and output_path.read_bytes()
            == calculation_canonical_json_bytes(result)
        )
        canonical_byte_checks["calculation_manifest_bytes"] = (
            manifest is not None
            and manifest_path.read_bytes()
            == calculation_canonical_json_bytes(manifest)
        )
        canonical_byte_checks["execution_report_bytes"] = (
            execution_report is not None
            and execution_report_path.read_bytes()
            == report_json_bytes(execution_report)
        )
    except (TypeError, ValueError):
        pass
    canonical_bytes_match = all(canonical_byte_checks.values())
    if not canonical_bytes_match:
        mismatch_codes.append("canonicalization_mismatch")

    fresh_result: dict[str, Any] | None = None
    independent_regeneration_match = False
    independent_regenerated_output_sha256: str | None = None
    try:
        fresh_result = rebuild_calculation_result()
        fresh_result_bytes = calculation_canonical_json_bytes(fresh_result)
        independent_regenerated_output_sha256 = sha256_bytes(fresh_result_bytes)
        independent_regeneration_match = (
            fresh_result_bytes == output_path.read_bytes()
        )
    except (KeyError, TypeError, ValueError):
        independent_regeneration_match = False
    if not independent_regeneration_match:
        mismatch_codes.append("regeneration_mismatch")

    schema_match = False
    if all(artifact is not None for artifact in artifacts.values()):
        assert guardrail is not None
        assert result is not None
        assert manifest is not None
        assert execution_report is not None
        required_result_fields = {
            "schema_id",
            "calculation_id",
            "calculation_status",
            "background_geometry",
            "background_geometry_classification",
            "parameters",
            "curvature_verification",
            "on_shell",
            "off_shell",
            "negative_controls",
            "patch_domain_safety",
            "thresholds",
            "threshold_evidence",
            "threshold_checks",
            "all_thresholds_passed",
            "claim",
            "boundary",
        }
        required_manifest_fields = {
            "schema_id",
            "calculation_id",
            "guardrail_sha256",
            "script_sha256",
            "output_sha256",
            "canonical_json_contract",
            "background_geometry_classification",
            "result_review_target",
            "gravity_evolved",
            "einstein_tensor_source_tested",
            "two_dimensional_einstein_gravity_degenerate",
            "covariant_matter_identity_tested",
        }
        required_execution_fields = {
            "schema_id",
            "calculation_id",
            "status",
            "calculation_output_sha256",
            "calculation_manifest_sha256",
            "guardrail_sha256",
            "calculation_script_sha256",
            "curvature_verification",
            "negative_controls",
            "patch_domain_safety",
            "threshold_checks",
            "boundary",
        }
        schema_match = (
            guardrail.get("schema_id") == PACKET_SCHEMA_ID
            and guardrail.get("calculation_id") == CALCULATION_ID
            and guardrail.get("selected_next_target") == EXECUTION_TARGET
            and required_result_fields.issubset(result)
            and result.get("schema_id") == f"{CALCULATION_ID}-RESULT"
            and result.get("calculation_id") == CALCULATION_ID
            and result.get("calculation_status")
            == "executed_pending_result_review"
            and required_manifest_fields.issubset(manifest)
            and manifest.get("schema_id") == f"{CALCULATION_ID}-MANIFEST"
            and manifest.get("calculation_id") == CALCULATION_ID
            and manifest.get("result_review_target") == REVIEW_TARGET
            and required_execution_fields.issubset(execution_report)
            and execution_report.get("schema_id")
            == (
                "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
                "NONZERO_CURVATURE_BACKGROUND_CALCULATION_EXECUTION_"
                "20260709_v0"
            )
            and execution_report.get("calculation_id") == CALCULATION_ID
            and execution_report.get("status")
            == "executed_pending_result_review"
            and execution_report.get("selected_next_target") == REVIEW_TARGET
        )
    if not schema_match:
        mismatch_codes.append("schema_mismatch")

    manifest_hash_links_match = False
    execution_report_hash_links_match = False
    if manifest is not None:
        manifest_hash_links_match = (
            manifest.get("guardrail_sha256")
            == actual_hashes["guardrail_sha256"]
            and manifest.get("script_sha256") == actual_hashes["script_sha256"]
            and manifest.get("output_sha256") == actual_hashes["output_sha256"]
        )
    if not manifest_hash_links_match:
        mismatch_codes.append("manifest_hash_mismatch")
    if execution_report is not None:
        execution_report_hash_links_match = (
            execution_report.get("guardrail_sha256")
            == actual_hashes["guardrail_sha256"]
            and execution_report.get("calculation_script_sha256")
            == actual_hashes["script_sha256"]
            and execution_report.get("calculation_output_sha256")
            == actual_hashes["output_sha256"]
            and execution_report.get("calculation_manifest_sha256")
            == actual_hashes["manifest_sha256"]
        )
    if not execution_report_hash_links_match:
        mismatch_codes.append("execution_report_link_mismatch")

    expected_control_counts = {
        "time_slice_count": len(TIME_SLICES),
        "resolution_count": len(RESOLUTIONS),
        "on_shell_time_resolution_rows": len(TIME_SLICES) * len(RESOLUTIONS),
        "off_shell_time_resolution_rows": len(TIME_SLICES) * len(RESOLUTIONS),
        "on_shell_resolution_aggregates": len(RESOLUTIONS),
        "off_shell_resolution_aggregates": len(RESOLUTIONS),
        "curvature_analytic_rows": len(TIME_SLICES),
        "curvature_component_rows": len(TIME_SLICES),
        "curvature_omission_rows": len(TIME_SLICES),
        "curvature_verification_route_count": 2,
        "negative_control_count": 3,
        "frozen_threshold_count": 11,
        "divergence_component_count": 2,
    }
    observed_control_counts: dict[str, int] = {}
    count_match = False
    time_resolution_rows_exact_bytes_match = False
    resolution_aggregates_exact_bytes_match = False
    per_resolution_section_hashes: dict[str, dict[str, str]] = {}
    if result is not None and fresh_result is not None:
        try:
            curvature = result["curvature_verification"]
            observed_control_counts = {
                "time_slice_count": len(result["parameters"]["time_slices_eta"]),
                "resolution_count": len(result["parameters"]["resolutions_N"]),
                "on_shell_time_resolution_rows": len(
                    result["on_shell"]["time_slice_results"]
                ),
                "off_shell_time_resolution_rows": len(
                    result["off_shell"]["time_slice_results"]
                ),
                "on_shell_resolution_aggregates": len(
                    result["on_shell"]["resolution_aggregates"]
                ),
                "off_shell_resolution_aggregates": len(
                    result["off_shell"]["resolution_aggregates"]
                ),
                "curvature_analytic_rows": len(
                    curvature["analytic_conformal_route"]["rows"]
                ),
                "curvature_component_rows": len(
                    curvature["independent_component_route"]["rows"]
                ),
                "curvature_omission_rows": len(
                    curvature["curvature_derivative_omission_negative_control"][
                        "rows"
                    ]
                ),
                "curvature_verification_route_count": 2,
                "negative_control_count": len(result["negative_controls"]),
                "frozen_threshold_count": result["frozen_threshold_count"],
                "divergence_component_count": 2,
            }
            expected_row_pairs = [
                (resolution, eta)
                for resolution in RESOLUTIONS
                for eta in TIME_SLICES
            ]
            count_match = (
                observed_control_counts == expected_control_counts
                and result["parameters"]["time_slices_eta"] == list(TIME_SLICES)
                and result["parameters"]["resolutions_N"] == list(RESOLUTIONS)
                and all(
                    [
                        (row["resolution_N"], row["time_eta"])
                        for row in result[control]["time_slice_results"]
                    ]
                    == expected_row_pairs
                    for control in ("on_shell", "off_shell")
                )
                and all(
                    [
                        row["resolution_N"]
                        for row in result[control]["resolution_aggregates"]
                    ]
                    == list(RESOLUTIONS)
                    for control in ("on_shell", "off_shell")
                )
            )
            for control in ("on_shell", "off_shell"):
                for section in ("time_slice_results", "resolution_aggregates"):
                    observed_hash = _json_fragment_sha256(
                        result[control][section]
                    )
                    regenerated_hash = _json_fragment_sha256(
                        fresh_result[control][section]
                    )
                    per_resolution_section_hashes[f"{control}_{section}"] = {
                        "observed_sha256": observed_hash,
                        "independently_regenerated_sha256": regenerated_hash,
                    }
            time_resolution_rows_exact_bytes_match = all(
                hashes["observed_sha256"]
                == hashes["independently_regenerated_sha256"]
                for name, hashes in per_resolution_section_hashes.items()
                if name.endswith("time_slice_results")
            )
            resolution_aggregates_exact_bytes_match = all(
                hashes["observed_sha256"]
                == hashes["independently_regenerated_sha256"]
                for name, hashes in per_resolution_section_hashes.items()
                if name.endswith("resolution_aggregates")
            )
        except (KeyError, TypeError):
            count_match = False
    if not count_match:
        mismatch_codes.append("count_mismatch")
    if not (
        time_resolution_rows_exact_bytes_match
        and resolution_aggregates_exact_bytes_match
    ):
        mismatch_codes.append("row_aggregate_mismatch")

    threshold_match = False
    threshold_evidence: dict[str, Any] = {}
    threshold_checks: dict[str, Any] = {}
    if (
        guardrail is not None
        and result is not None
        and fresh_result is not None
        and execution_report is not None
    ):
        try:
            thresholds = guardrail["success_criteria"]
            threshold_evidence = result["threshold_evidence"]
            threshold_checks = result["threshold_checks"]
            recomputed_checks = _recompute_threshold_checks(
                threshold_evidence, thresholds
            )
            threshold_match = (
                result["thresholds"] == thresholds
                and result["frozen_threshold_count"] == 11
                and len(threshold_checks) == 11
                and threshold_checks == recomputed_checks
                and all(threshold_checks.values())
                and result["all_thresholds_passed"] is True
                and threshold_evidence == fresh_result["threshold_evidence"]
                and threshold_checks == fresh_result["threshold_checks"]
                and execution_report["threshold_evidence"] == threshold_evidence
                and execution_report["threshold_checks"] == threshold_checks
                and execution_report["all_thresholds_passed"] is True
                and execution_report["control_counts"]["frozen_threshold_count"]
                == 11
            )
        except (KeyError, TypeError):
            threshold_match = False
    if not threshold_match:
        mismatch_codes.append("threshold_mismatch")

    curvature_routes_match = False
    curvature_evidence: dict[str, Any] = {}
    if (
        result is not None
        and fresh_result is not None
        and execution_report is not None
    ):
        try:
            curvature_evidence = result["curvature_verification"]
            analytic_rows = curvature_evidence["analytic_conformal_route"]["rows"]
            component_rows = curvature_evidence["independent_component_route"][
                "rows"
            ]
            curvature_routes_match = (
                [row["time_eta"] for row in analytic_rows] == list(TIME_SLICES)
                and [row["time_eta"] for row in component_rows]
                == list(TIME_SLICES)
                and all(
                    abs(row["scalar_curvature"] - 0.08) <= 1e-12
                    for row in analytic_rows + component_rows
                )
                and all(
                    row["nonzero_connection_component_count"] == 4
                    and row["ricci_relation_max_absolute_error"] <= 1e-12
                    for row in component_rows
                )
                and curvature_evidence[
                    "maximum_route_agreement_absolute_error"
                ]
                <= 1e-12
                and curvature_evidence[
                    "minimum_absolute_measured_scalar_curvature"
                ]
                >= 0.05
                and curvature_evidence["ricci_relation_max_absolute_error"]
                <= 1e-12
                and curvature_evidence["scalar_curvature_expected"] == 0.08
                and curvature_evidence["scalar_curvature_measured"] == 0.08
                and curvature_evidence == fresh_result["curvature_verification"]
                and execution_report["curvature_verification"]
                == curvature_evidence
            )
        except (KeyError, TypeError):
            curvature_routes_match = False
    if not curvature_routes_match:
        mismatch_codes.append("curvature_route_mismatch")

    negative_controls_match = False
    negative_control_evidence: dict[str, Any] = {}
    if (
        result is not None
        and fresh_result is not None
        and execution_report is not None
    ):
        try:
            negative_control_evidence = result["negative_controls"]
            expected_negative_control_names = {
                "naive_partial_divergence",
                "inconsistent_frozen_connection",
                "curvature_derivative_omission",
            }
            negative_controls_match = (
                set(negative_control_evidence) == expected_negative_control_names
                and all(
                    negative_control_evidence[name]["failure_detected"] is True
                    for name in expected_negative_control_names
                )
                and negative_control_evidence["naive_partial_divergence"][
                    "finest_on_shell_error_ratio"
                ]
                >= 100.0
                and negative_control_evidence[
                    "inconsistent_frozen_connection"
                ]["minimum_finest_on_off_error_ratio"]
                >= 50.0
                and negative_control_evidence["curvature_derivative_omission"][
                    "minimum_absolute_discrepancy_from_correct_route"
                ]
                >= 0.04
                and negative_control_evidence["curvature_derivative_omission"]
                == result["curvature_verification"][
                    "curvature_derivative_omission_negative_control"
                ]
                and negative_control_evidence
                == fresh_result["negative_controls"]
                and execution_report["negative_controls"]
                == negative_control_evidence
            )
        except (KeyError, TypeError):
            negative_controls_match = False
    if not negative_controls_match:
        mismatch_codes.append("negative_control_mismatch")

    patch_safety_match = False
    patch_safety_evidence: dict[str, Any] = {}
    if (
        guardrail is not None
        and result is not None
        and fresh_result is not None
        and execution_report is not None
    ):
        try:
            patch_safety_evidence = result["patch_domain_safety"]
            patch_safety_match = (
                patch_safety_evidence == fresh_result["patch_domain_safety"]
                and execution_report["patch_domain_safety"]
                == patch_safety_evidence
                and result["parameters"]["eta_domain"] == [0.0, 1.0]
                and guardrail["inputs"]["coordinate_domain"]["eta"]
                == "eta in [0,1]"
                and patch_safety_evidence["eta_domain"] == [0.0, 1.0]
                and patch_safety_evidence["coordinate_patch_singularity_eta"]
                == 5.0
                and patch_safety_evidence[
                    "minimum_one_minus_H_eta_over_domain"
                ]
                == 0.8
                and patch_safety_evidence["maximum_scale_factor_over_domain"]
                == 1.25
                and patch_safety_evidence[
                    "minimum_coordinate_distance_to_patch_singularity_over_domain"
                ]
                == 4.0
                and patch_safety_evidence["strictly_inside_coordinate_patch"]
                is True
                and patch_safety_evidence[
                    "coordinate_patch_boundary_is_physical_curvature_singularity"
                ]
                is False
                and patch_safety_evidence[
                    "sampled_minimum_one_minus_H_eta"
                ]
                >= 0.8
                and patch_safety_evidence["sampled_maximum_scale_factor"] <= 1.25
                and patch_safety_evidence[
                    "sampled_minimum_coordinate_distance_to_patch_singularity"
                ]
                >= 4.0
            )
        except (KeyError, TypeError):
            patch_safety_match = False
    if not patch_safety_match:
        mismatch_codes.append("patch_safety_mismatch")

    geometry_match = False
    if (
        guardrail is not None
        and result is not None
        and fresh_result is not None
        and manifest is not None
        and execution_report is not None
    ):
        try:
            background = result["background_geometry"]
            geometry_match = (
                result["background_geometry_classification"]
                == BACKGROUND_GEOMETRY_CLASSIFICATION
                and background == fresh_result["background_geometry"]
                and background["background_geometry_classification"]
                == BACKGROUND_GEOMETRY_CLASSIFICATION
                and background["guardrail_geometry_classification"]
                == GUARDRAIL_GEOMETRY_CLASSIFICATION
                and background["metric_signature"] == "(-,+)"
                and background["scalar_curvature_expected"] == 0.08
                and background["scalar_curvature_measured"] == 0.08
                and background["genuinely_nonzero_curvature_test_executed"]
                is True
                and background["curvature_test_claimed"] is True
                and background["covariant_connection_test_claimed"] is True
                and guardrail["background_geometry"]["classification"]
                == GUARDRAIL_GEOMETRY_CLASSIFICATION
                and guardrail["background_geometry"]["scalar_curvature"] == 0.08
                and manifest["background_geometry_classification"]
                == BACKGROUND_GEOMETRY_CLASSIFICATION
                and manifest["scalar_curvature_expected"] == 0.08
                and manifest["scalar_curvature_measured"] == 0.08
                and execution_report["background_geometry_classification"]
                == BACKGROUND_GEOMETRY_CLASSIFICATION
                and execution_report["guardrail_geometry_classification"]
                == GUARDRAIL_GEOMETRY_CLASSIFICATION
                and execution_report["scalar_curvature_expected"] == 0.08
                and execution_report["scalar_curvature_measured"] == 0.08
                and result["on_shell"]["forced_or_manufactured"] is False
                and result["on_shell"]["exact_residual"] == "E_phi = 0"
                and result["off_shell"]["forced_or_manufactured"] is False
            )
        except (KeyError, TypeError):
            geometry_match = False
    if not geometry_match:
        mismatch_codes.append("geometry_classification_mismatch")

    on_shell_absolute_error_policy_match = False
    if guardrail is not None and result is not None and fresh_result is not None:
        try:
            on_shell_absolute_error_policy_match = (
                result["on_shell"]["relative_error_against_zero_formed"]
                is False
                and fresh_result["on_shell"][
                    "relative_error_against_zero_formed"
                ]
                is False
                and guardrail["numerical_method"]["on_shell_error_policy"]
                == (
                    "report absolute covariant-divergence norms; no relative "
                    "error against a zero reference"
                )
            )
        except (KeyError, TypeError):
            on_shell_absolute_error_policy_match = False
    if not on_shell_absolute_error_policy_match:
        mismatch_codes.append("on_shell_error_policy_mismatch")

    solution_controls_match = False
    if guardrail is not None and result is not None and fresh_result is not None:
        try:
            solution_controls_match = (
                guardrail["solution_controls"]["on_shell_positive_control"]
                == {
                    "omega": 2.0,
                    "classification": "exact_source_free_solution",
                    "forced_or_manufactured": False,
                    "exact_residual": "E_phi = 0",
                }
                and guardrail["solution_controls"]["off_shell_control"]
                == {
                    "omega": 2.2,
                    "classification": "deliberately_off_shell_unforced_field",
                    "forced_or_manufactured": False,
                    "exact_residual": (
                        "E_phi = 0.84 * a(eta)^(-2) * phi"
                    ),
                }
                and result["on_shell"]["control_role"]
                == "exact source-free covariant-conservation control"
                and result["on_shell"]["forced_or_manufactured"] is False
                and result["on_shell"]["exact_residual"] == "E_phi = 0"
                and result["off_shell"]["control_role"]
                == "deliberately off-shell unforced residual control"
                and result["off_shell"]["forced_or_manufactured"] is False
                and result["off_shell"]["exact_reference"]
                == "E_phi = 0.84 * a(eta)^(-2) * phi"
                and result["parameters"][
                    "exact_off_shell_coefficient_before_a_inverse_squared"
                ]
                == 0.84
                and result["on_shell"] == fresh_result["on_shell"]
                and result["off_shell"] == fresh_result["off_shell"]
            )
        except (KeyError, TypeError):
            solution_controls_match = False
    if not solution_controls_match:
        mismatch_codes.append("solution_control_mismatch")

    boundary_nonclaims_match = False
    boundary_evidence: dict[str, Any] = {}
    if (
        result is not None
        and fresh_result is not None
        and manifest is not None
        and execution_report is not None
    ):
        try:
            boundary_evidence = result["boundary"]
            required_true_boundary = {
                "calculation_executed",
                "two_dimensional_einstein_gravity_degenerate",
                "einstein_tensor_identically_zero_in_two_dimensions",
                "covariant_matter_identity_tested",
                "genuine_nonzero_curvature_test_executed",
                "curvature_test_claimed",
            }
            required_false_boundary = {
                "gravity_evolved",
                "background_metric_evolved",
                "einstein_equation_solved",
                "einstein_tensor_source_tested",
                "ordinary_einstein_scalar_dynamics_claimed",
                "source_admissibility_claimed",
                "bianchi_compatibility_claimed",
                "qft_gr_seam_admissibility_claimed",
                "qft_gr_seam_closure_claimed",
                "quantum_stress_energy_source_claimed",
                "multi_background_robustness_claimed",
                "higher_dimensional_robustness_claimed",
                "pillar_completion_claimed",
                "ccft_resumed",
                "ccft_validated",
                "master_action_promoted",
            }
            boundary_nonclaims_match = (
                boundary_evidence == fresh_result["boundary"]
                and execution_report["boundary"] == boundary_evidence
                and all(
                    boundary_evidence[name] is True
                    for name in required_true_boundary
                )
                and all(
                    boundary_evidence[name] is False
                    for name in required_false_boundary
                )
                and result["gravity_evolved"] is False
                and result["einstein_tensor_source_tested"] is False
                and result["two_dimensional_einstein_gravity_degenerate"]
                is True
                and result["covariant_matter_identity_tested"] is True
                and manifest["gravity_evolved"] is False
                and manifest["einstein_tensor_source_tested"] is False
                and manifest["two_dimensional_einstein_gravity_degenerate"]
                is True
                and manifest["covariant_matter_identity_tested"] is True
                and execution_report["gravity_evolved"] is False
                and execution_report["einstein_tensor_source_tested"] is False
                and execution_report[
                    "two_dimensional_einstein_gravity_degenerate"
                ]
                is True
                and execution_report["covariant_matter_identity_tested"] is True
                and result["claim"]["primary_label"] == "E-REPRO"
                and result["claim"]["claim_ceiling_level"] == 3
                and result["claim"]["claim_status"]
                == "generated_pending_result_review"
                and result["claim"]["next_work_status"] == REVIEW_TARGET
                and result["result_review"]["target"] == REVIEW_TARGET
                and result["equation_compendium_edited"] is False
                and result["existing_equation_id_reused"] == EQUATION_ID
            )
        except (KeyError, TypeError):
            boundary_nonclaims_match = False
    if not boundary_nonclaims_match:
        mismatch_codes.append("boundary_nonclaim_mismatch")

    mismatch_codes = list(dict.fromkeys(mismatch_codes))
    accepted = not mismatch_codes
    return {
        "accepted": accepted,
        "primary_claim_label": "E-REPRO" if accepted else "B-BLOCKED",
        "claim_status": (
            "accepted_level_3_scoped_e_repro_fixed_1plus1_de_sitter_"
            "matter_identity_only"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "mismatch_codes": mismatch_codes,
        "expected_hashes": EXPECTED_EXECUTION_HASHES,
        "actual_hashes": actual_hashes,
        "all_five_execution_artifact_hashes_match": (
            actual_hashes == EXPECTED_EXECUTION_HASHES
        ),
        "manifest_hash_links_match": manifest_hash_links_match,
        "execution_report_hash_links_match": execution_report_hash_links_match,
        "canonical_byte_checks": canonical_byte_checks,
        "canonical_bytes_match": canonical_bytes_match,
        "independent_in_memory_regeneration_match": (
            independent_regeneration_match
        ),
        "independent_regenerated_output_sha256": (
            independent_regenerated_output_sha256
        ),
        "schema_match": schema_match,
        "expected_control_counts": expected_control_counts,
        "observed_control_counts": observed_control_counts,
        "all_row_and_aggregate_counts_match": count_match,
        "time_resolution_rows_exact_bytes_match": (
            time_resolution_rows_exact_bytes_match
        ),
        "resolution_aggregates_exact_bytes_match": (
            resolution_aggregates_exact_bytes_match
        ),
        "per_resolution_results_match": (
            count_match
            and time_resolution_rows_exact_bytes_match
            and resolution_aggregates_exact_bytes_match
        ),
        "per_resolution_section_hashes": per_resolution_section_hashes,
        "all_eleven_thresholds_match": threshold_match,
        "threshold_evidence": threshold_evidence,
        "threshold_checks": threshold_checks,
        "both_curvature_routes_match": curvature_routes_match,
        "curvature_verification": curvature_evidence,
        "all_three_negative_controls_match": negative_controls_match,
        "negative_controls": negative_control_evidence,
        "patch_domain_safety_match": patch_safety_match,
        "patch_domain_safety": patch_safety_evidence,
        "background_geometry_classification_match": geometry_match,
        "on_shell_absolute_error_policy_match": (
            on_shell_absolute_error_policy_match
        ),
        "on_shell_and_off_shell_controls_match": solution_controls_match,
        "two_dimensional_einstein_degeneracy_and_nonclaims_match": (
            boundary_nonclaims_match
        ),
        "boundary": boundary_evidence,
        "selected_next_target": (
            HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_TARGET
            if accepted
            else REPRODUCIBILITY_REPAIR_TARGET
        ),
    }


def build_review_report(**verification_paths: Path) -> dict[str, Any]:
    verification = verify_calculation_result(**verification_paths)
    accepted = verification["accepted"]
    return {
        "schema_id": (
            "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
            "CURVATURE_BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0"
        ),
        "review_id": (
            "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_"
            "CURVATURE_BACKGROUND_CALCULATION_RESULT_REVIEW_v0"
        ),
        "status": (
            "accepted_scoped_e_repro"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": REVIEW_TARGET,
        "consumed_target_kind": REVIEW_TARGET_KIND,
        "selected_next_target": verification["selected_next_target"],
        "selected_next_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_higher_"
            "dimensional_curved_background_guardrail_packet"
            if accepted
            else "nonzero_curvature_background_v0_reproducibility_repair"
        ),
        "packet_result": REVIEW_OUTCOME if accepted else "B-BLOCKED",
        "strict_packet_result": REVIEW_STRICT_OUTCOME if accepted else "B-BLOCKED",
        "review_result": REVIEW_OUTCOME if accepted else "B-BLOCKED",
        "strict_review_result": (
            REVIEW_STRICT_OUTCOME if accepted else "B-BLOCKED"
        ),
        "verification": verification,
        "background_geometry": {
            "background_geometry_classification": (
                BACKGROUND_GEOMETRY_CLASSIFICATION
            ),
            "guardrail_geometry_classification": (
                GUARDRAIL_GEOMETRY_CLASSIFICATION
            ),
            "dimension": 2,
            "scalar_curvature_expected": 0.08,
            "scalar_curvature_measured": 0.08,
            "fixed_background_only": True,
            "genuine_nonzero_curvature_validated": accepted,
            "covariant_matter_identity_tested": accepted,
        },
        "claim": {
            "primary_label": verification["primary_claim_label"],
            "claim_status": verification["claim_status"],
            "claim_ceiling_level": 3,
            "claim_scope": (
                "scoped E-REPRO for the scalar covariant stress-energy "
                "divergence identity on one fixed genuinely curved 1+1 "
                "de Sitter background"
            ),
        },
        "execution_artifacts_modified_by_review": False,
        "on_shell_error_presentation_note": {
            "policy": "absolute covariant-divergence norms against a zero reference",
            "relative_error_against_zero_formed": False,
            "serialized_relative_error_fields": (
                "floor-normalized diagnostics only; do not interpret or cite as "
                "on-shell relative errors"
            ),
            "threshold_dependency": False,
            "review_effect": "nonblocking",
        },
        "existing_equation_id_reused": EQUATION_ID,
        "equation_surface_status": (
            "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"
        ),
        "equation_surface_upgraded_by_review": False,
        "equation_compendium_edited_by_review": False,
        "gravity_evolved": False,
        "einstein_tensor_source_tested": False,
        "two_dimensional_einstein_gravity_degenerate": True,
        "covariant_matter_identity_tested": accepted,
        "ccft_lane_status": "paused_upstream_prerequisites",
        "remaining_blockers": [
            "no structurally distinct higher-dimensional curved-background witness",
            "no multi-background robustness synthesis",
            "no dynamical gravity or Einstein-scalar evolution",
            "no GR source admissibility",
            "no Bianchi compatibility",
            "no QFT-GR seam admissibility or closure",
            "no quantum or renormalized stress-energy source",
            "no master-action promotion",
        ],
        "boundary": {
            "single_fixed_1plus1_de_sitter_matter_identity_accepted": accepted,
            "genuine_nonzero_curvature_validated": accepted,
            "two_dimensional_einstein_gravity_degenerate": True,
            "einstein_tensor_identically_zero_in_two_dimensions": True,
            "gravity_dynamics_validated": False,
            "einstein_source_tested": False,
            "general_curved_spacetime_identity_claimed": False,
            "higher_dimensional_robustness_claimed": False,
            "multi_background_robustness_claimed": False,
            "source_admissibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "pillar_completion_claimed": False,
            "ccft_resumed": False,
            "ccft_validated": False,
            "master_action_promoted": False,
        },
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def write_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(report_json_bytes(payload))


def guardrail_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the scalar nonzero-curvature background guardrail."
    )
    parser.add_argument("--out", type=Path, default=GUARDRAIL_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "outcome": GUARDRAIL_OUTCOME,
                "scalar_curvature": payload["background_geometry"][
                    "scalar_curvature"
                ],
                "selected_next_target": EXECUTION_TARGET,
            }
        )
    )
    return 0


def execution_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Record the fixed 1+1 de Sitter scalar execution."
    )
    parser.add_argument("--out", type=Path, default=EXECUTION_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_execution_report()
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "outcome": EXECUTION_OUTCOME,
                "background_geometry_classification": payload[
                    "background_geometry_classification"
                ],
                "scalar_curvature_measured": payload[
                    "scalar_curvature_measured"
                ],
                "calculation_output_sha256": payload[
                    "calculation_output_sha256"
                ],
                "calculation_manifest_sha256": payload[
                    "calculation_manifest_sha256"
                ],
                "selected_next_target": REVIEW_TARGET,
            },
            sort_keys=True,
        )
    )
    return 0


def review_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the fixed 1+1 de Sitter scalar matter-identity calculation."
        )
    )
    parser.add_argument("--out", type=Path, default=REVIEW_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_review_report()
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "accepted": payload["verification"]["accepted"],
                "outcome": payload["packet_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            sort_keys=True,
        )
    )
    return 0 if payload["verification"]["accepted"] else 1
