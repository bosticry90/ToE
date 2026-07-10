from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


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

BACKGROUND_GEOMETRY_CLASSIFICATION = (
    "fixed_nonzero_curvature_1plus1_de_sitter_patch"
)
GUARDRAIL_GEOMETRY_CLASSIFICATION = (
    "fixed_1_plus_1_de_sitter_conformal_patch"
)
EXPECTED_GUARDRAIL_SHA256 = (
    "3670bfaa98876b32e95f5ff7406546a41aa691f937fe738fee6e3ab36a399191"
)


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
