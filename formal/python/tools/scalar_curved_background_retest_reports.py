from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.toe.calculations.calc_scalar_stress_energy_covariant_divergence_identity_conformal_background import (
    CALCULATION_ID,
    RESOLUTIONS,
    TIME_SLICES,
    build_result as rebuild_calculation_result,
    canonical_json_bytes as calculation_canonical_json_bytes,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"

GUARDRAIL_TARGET = (
    "prepare_bounded_curved_space_scalar_qft_gr_source_contract_retest_"
    "guardrail_packet"
)
EXECUTION_TARGET = (
    "execute_calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background_v0"
)
REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background_v0_result"
)
THRESHOLD_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background_v0_threshold_failure"
)
REPRODUCIBILITY_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background_v0_reproducibility_mismatch"
)
NONZERO_CURVATURE_GUARDRAIL_TARGET = (
    "prepare_scalar_stress_energy_covariant_divergence_identity_nonzero_"
    "curvature_background_guardrail_packet"
)

GUARDRAIL_OUTCOME = (
    "BOUNDED_CURVED_SPACE_SCALAR_QFT_GR_SOURCE_CONTRACT_RETEST_GUARDRAIL_"
    "PACKET_PREPARED_AUTHORIZES_FIXED_CONFORMAL_BACKGROUND_COVARIANT_"
    "DIVERGENCE_IDENTITY_CALCULATION_ONLY"
)
GUARDRAIL_STRICT_OUTCOME = (
    "BOUNDED_CURVED_SPACE_SCALAR_QFT_GR_SOURCE_CONTRACT_RETEST_GUARDRAIL_"
    "PACKET_PREPARED_LEVEL_3_FIXED_BACKGROUND_PRETEST_ONLY_NO_GRAVITY_"
    "EVOLUTION_NO_SOURCE_ADMISSIBILITY_NO_BIANCHI_OR_SEAM_ADMISSIBILITY_"
    "NO_MASTER_ACTION_PROMOTION"
)
EXECUTION_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_BACKGROUND_"
    "CALCULATION_EXECUTED_PASSES_LEVEL_3_CONNECTION_COVARIANCE_CONTROLS_"
    "PENDING_RESULT_REVIEW"
)
EXECUTION_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_BACKGROUND_"
    "CALCULATION_EXECUTED_SCOPED_E_REPRO_PENDING_REVIEW_LOCALLY_FLAT_"
    "BACKGROUND_ONLY_NO_CURVATURE_TEST_NO_SOURCE_ADMISSIBILITY_NO_BIANCHI_"
    "OR_SEAM_ADMISSIBILITY_NO_MASTER_ACTION_PROMOTION"
)
REVIEW_OUTCOME = (
    "CALC_SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_"
    "BACKGROUND_RESULT_REVIEW_ACCEPTS_REPRODUCIBLE_LOCALLY_FLAT_NONTRIVIAL_"
    "CONNECTION_TEST_ONLY_NO_CURVATURE_OR_SOURCE_ADMISSIBILITY_CLAIM"
)
REVIEW_STRICT_OUTCOME = (
    "CALC_SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_"
    "BACKGROUND_RESULT_REVIEW_ACCEPTS_SCOPED_E_REPRO_FOR_COVARIANT_"
    "CONNECTION_IDENTITY_ONLY_NO_BIANCHI_COMPATIBILITY_NO_QFT_GR_SEAM_"
    "ADMISSIBILITY_NO_MASTER_ACTION_PROMOTION"
)

GUARDRAIL_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "BOUNDED_CURVED_SPACE_SCALAR_QFT_GR_SOURCE_CONTRACT_RETEST_"
    "GUARDRAIL_PACKET_20260709_v0.json"
)
QM_PRESSURE_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_REAL_COMPLEX_REPRESENTATION_LITERATURE_PRESSURE_20260709_v0.json"
)
READINESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
MINKOWSKI_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_"
    "RESULT_REVIEW_20260709_v0.json"
)
CALCULATION_OUTPUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "CONFORMAL-BACKGROUND-v0.json"
)
CALCULATION_MANIFEST_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "CONFORMAL-BACKGROUND-MANIFEST-v0.json"
)
EXECUTION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_"
    "BACKGROUND_CALCULATION_EXECUTION_20260709_v0.json"
)
CALCULATION_SCRIPT_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "toe"
    / "calculations"
    / "calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background.py"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_"
    "BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0.json"
)

EXPECTED_EXECUTION_HASHES = {
    "guardrail_sha256": (
        "0e16434fca7015b8f2f1c5096050dc05d75904ec34f6cba38c63e33227679f63"
    ),
    "script_sha256": (
        "5ecc11be6538a9f266a671bff92e2e143d592c7426e89033a2185374420ae399"
    ),
    "output_sha256": (
        "1141870b5a83289a7fc36b32a5375f2a48c96070e15b87c05f17ecfa88e62922"
    ),
    "manifest_sha256": (
        "06e609823aea3237d32136f450005458d27f6b985f07f910fd3d37be321c6b79"
    ),
    "execution_report_sha256": (
        "38746a5089013c5d0044962318409c072b81defd0b54e680f7aedfcbcee5e4b9"
    ),
}

PROPOSED_EQUATION_ID = (
    "EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0"
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


def build_qm_representation_pressure() -> dict[str, Any]:
    return {
        "schema_id": "QM_REAL_COMPLEX_REPRESENTATION_LITERATURE_PRESSURE_20260709_v0",
        "pressure_id": "quantum_representation_number_field_nonuniqueness",
        "captured_at_utc": CAPTURED_AT_UTC,
        "status": "external_literature_pressure_active_foundational_debate",
        "provenance_status": "supplied_review_summary_not_independently_adopted",
        "claim_upgrade": False,
        "active_lane_interrupted": False,
        "foundational_question": (
            "Can the ToE derive the structure represented by i rather than "
            "merely choosing complex or doubled-real notation?"
        ),
        "representation_neutral_requirements": [
            "state map",
            "operator map",
            "observable map",
            "composition rule",
            "probability preservation",
            "dynamics preservation",
            "locality preservation",
            "distinguished real operator J with J^2 = -I when required",
        ],
        "debate_sides_retained": [
            "real-formulation equivalence arguments",
            "hidden-complex-structure critique",
        ],
        "literature_locators": [
            "https://arxiv.org/abs/2503.17307",
            "https://arxiv.org/abs/2607.05865",
            "https://arxiv.org/abs/2101.10873",
            "https://arxiv.org/abs/2603.19208",
        ],
        "future_sprint_sequence": [
            "prepare_qm_real_complex_representation_equivalence_calculation_sprint_guardrail_packet",
            "execute_calc_qm_real_complex_representation_equivalence_v0",
            "review_calc_qm_real_complex_representation_equivalence_v0_result",
        ],
        "future_calculation_controls": [
            "finite-dimensional complex Schrodinger system",
            "doubled-real state and operator map",
            "probability and expectation-value preservation",
            "two-system composition example",
            "naive ordinary-real tensor-product negative control",
            "corrected balanced or symplectic composition control",
        ],
        "nonclaims": [
            "complex structure eliminated from quantum mechanics",
            "quantum mechanics is classical",
            "ToE derives quantum mechanics",
            "CCFT is quantum or validated",
            "master action validated or promoted",
        ],
        "selected_as_current_target": False,
        "monthly_watch_created": False,
    }


def build_guardrail_payload(
    qm_pressure: dict[str, Any] | None = None,
) -> dict[str, Any]:
    pressure = qm_pressure or build_qm_representation_pressure()
    pressure_hash = sha256_bytes(report_json_bytes(pressure))
    return {
        "schema_id": (
            "BOUNDED_CURVED_SPACE_SCALAR_QFT_GR_SOURCE_CONTRACT_RETEST_"
            "GUARDRAIL_PACKET_20260709_v0"
        ),
        "packet_id": (
            "BOUNDED_CURVED_SPACE_SCALAR_QFT_GR_SOURCE_CONTRACT_RETEST_"
            "GUARDRAIL_PACKET_v0"
        ),
        "status": "prepared_authorizes_execution_only",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": GUARDRAIL_TARGET,
        "consumed_target_kind": (
            "bounded_curved_space_scalar_qft_gr_source_contract_retest_"
            "guardrail_packet"
        ),
        "selected_next_target": EXECUTION_TARGET,
        "selected_next_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_conformal_"
            "background_calculation_execution"
        ),
        "packet_result": GUARDRAIL_OUTCOME,
        "strict_packet_result": GUARDRAIL_STRICT_OUTCOME,
        "accepted_predecessor": {
            "artifact_id": (
                "SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_"
                "CALCULATION_RESULT_REVIEW_v0"
            ),
            "path": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_"
                "MINKOWSKI_CALCULATION_RESULT_REVIEW_20260709_v0.json"
            ),
            "sha256": sha256_path(MINKOWSKI_REVIEW_PATH),
            "accepted_claim_ceiling": "Level 3 toy-model demonstration",
        },
        "readiness_authority": {
            "artifact_id": "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0",
            "path": (
                "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
            ),
            "sha256": sha256_path(READINESS_PATH),
            "status": "accepted_current_science_sprint_readiness_authority",
        },
        "deferred_qm_representation_pressure": {
            "artifact_id": pressure["pressure_id"],
            "path": (
                "formal/docs/release/QM_REAL_COMPLEX_REPRESENTATION_"
                "LITERATURE_PRESSURE_20260709_v0.json"
            ),
            "sha256": pressure_hash,
            "status": pressure["status"],
            "selected_as_current_target": False,
            "claim_upgrade": False,
        },
        "question": (
            "Does the scalar covariant stress-energy divergence identity hold "
            "numerically for on-shell and deliberately off-shell controls on a "
            "fixed conformally flat background?"
        ),
        "inputs": {
            "coordinates": ["eta", "x"],
            "dimension": 2,
            "spatial_domain": "x in [0,2*pi), periodic",
            "time_slices_eta": [0.0, 0.37, 0.91],
            "spatial_resolutions_N": [64, 128, 256, 512],
            "scale_factor": "a(eta) = exp(H * eta)",
            "conformal_rate_H": 0.2,
            "field": "phi(eta,x) = A cos(k*x - omega*eta)",
            "amplitude_A": 0.2,
            "wave_number_k": 2.0,
            "mass_m": 0.0,
            "omega_on": 2.0,
            "omega_off": 2.2,
            "off_shell_exact_coefficient": 0.84,
            "off_shell_exact_residual": "E_phi = 0.84 * a(eta)^(-2) * phi",
        },
        "equation_surfaces": {
            "metric": "g_mu_nu = a(eta)^2 * diag(-1,+1)",
            "inverse_metric": "g^mu_nu = a(eta)^(-2) * diag(-1,+1)",
            "metric_signature": "(-,+)",
            "volume_density": "sqrt(-g) = a(eta)^2",
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
                "partial_nu phi] = a^(-2)(-partial_eta^2 + partial_x^2) phi"
            ),
            "covariant_divergence": (
                "nabla_mu T^{mu nu} = partial_mu T^{mu nu} + "
                "Gamma^mu_{mu lambda} T^{lambda nu} + "
                "Gamma^nu_{mu lambda} T^{mu lambda}"
            ),
            "identity": (
                "nabla_mu T^{mu nu} = E_phi nabla^nu phi"
            ),
            "proposed_equation_id_pending_review": PROPOSED_EQUATION_ID,
            "equation_compendium_edited": False,
        },
        "connection_and_curvature_conventions": {
            "christoffel_definition": (
                "Gamma^rho_{mu nu} = 1/2 g^{rho sigma} "
                "(partial_mu g_{sigma nu} + partial_nu g_{sigma mu} - "
                "partial_sigma g_{mu nu})"
            ),
            "nonzero_christoffels": {
                "Gamma^eta_{eta eta}": "H",
                "Gamma^eta_{x x}": "H",
                "Gamma^x_{eta x}": "H",
                "Gamma^x_{x eta}": "H",
            },
            "riemann_sign": (
                "R^rho_{sigma mu nu} = partial_mu Gamma^rho_{nu sigma} - "
                "partial_nu Gamma^rho_{mu sigma} + "
                "Gamma^rho_{mu lambda} Gamma^lambda_{nu sigma} - "
                "Gamma^rho_{nu lambda} Gamma^lambda_{mu sigma}"
            ),
            "ricci_contraction": "R_{sigma nu} = R^rho_{sigma rho nu}",
            "curvature_used_as_dynamic_equation": False,
        },
        "assumptions": [
            "fixed prescribed conformally flat background",
            "real massless minimally coupled scalar specialization",
            "positive scale factor a(eta) = exp(0.2 eta)",
            "periodic spatial boundary",
            "analytic metric, connection, field, and temporal derivatives",
            "second-order numerical spatial flux derivatives only",
            "no metric evolution and no Einstein-equation solve",
        ],
        "units": {
            "convention": "dimensionless numerical test units with c = hbar = 1",
            "coordinate_parameter_consistency": (
                "eta, x, H, k, and omega use one natural-unit normalization"
            ),
            "physical_parameter_inference_allowed": False,
        },
        "allowed_operations": [
            "evaluate the prescribed metric, inverse metric, and connection",
            "evaluate analytic scalar and temporal derivatives",
            "apply second-order centered periodic spatial differences",
            "compute both nu=eta and nu=x covariant divergence components",
            "check metric compatibility nabla_lambda g_mu_nu = 0",
            "check H=0 flat-limit recovery against the Minkowski implementation",
            "compute component and combined RMS norms",
            "estimate convergence orders over the two finest refinement pairs",
            "write deterministic result, manifest, and execution report artifacts",
        ],
        "forbidden_claims": [
            "dynamical gravity or Einstein-equation solution",
            "general curved-spacetime theorem",
            "GR source admissibility",
            "Bianchi compatibility discharge",
            "QFT-GR seam admissibility or closure",
            "quantum or renormalized stress-energy source",
            "pillar completion",
            "CCFT validation or resumption",
            "master-action canonicalization, promotion, or closure",
        ],
        "numerical_method": {
            "temporal_derivatives": "analytic",
            "metric_and_connection_derivatives": "analytic",
            "spatial_derivatives": (
                "second-order centered periodic finite differences"
            ),
            "component_rms_norm": "sqrt(mean(v_nu^2))",
            "combined_rms_norm": "sqrt(mean(v_eta^2 + v_x^2))",
            "on_shell_error_policy": (
                "report absolute covariant-divergence norms; no relative error "
                "against a zero reference"
            ),
            "off_shell_identity_relative_error": (
                "norm(nabla_mu T^{mu nu} - E_phi nabla^nu phi) / "
                "max(norm(E_phi nabla^nu phi),1e-14)"
            ),
        },
        "required_controls": {
            "metric_compatibility": True,
            "flat_limit_recovery": True,
            "on_shell_positive_control": True,
            "off_shell_negative_control": True,
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
                "DIVERGENCE-IDENTITY-CONFORMAL-BACKGROUND-v0.json"
            ),
            "manifest": (
                "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-"
                "DIVERGENCE-IDENTITY-CONFORMAL-BACKGROUND-MANIFEST-v0.json"
            ),
            "execution_report": (
                "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_"
                "DIVERGENCE_IDENTITY_CONFORMAL_BACKGROUND_CALCULATION_"
                "EXECUTION_20260709_v0.json"
            ),
        },
        "claim_ceiling": {
            "claim_ladder_level": 3,
            "classification": "fixed-background toy-model demonstration",
            "execution_e_repro_status": "pending_result_review",
            "not_gravity_dynamics": True,
            "not_source_admissibility": True,
            "not_bianchi_compatibility": True,
            "not_seam_admissibility": True,
        },
        "reproduction_command": (
            "python -m formal.python.toe.calculations."
            "calc_scalar_stress_energy_covariant_divergence_identity_"
            "conformal_background"
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
        "e_repro_claimed": False,
        "equation_compendium_row_added": False,
        "ccft_lane_status": "paused_upstream_prerequisites",
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def validate_qm_representation_pressure(payload: dict[str, Any]) -> None:
    if payload.get("pressure_id") != (
        "quantum_representation_number_field_nonuniqueness"
    ):
        raise ValueError("QM representation pressure id differs")
    if payload.get("claim_upgrade") is not False:
        raise ValueError("QM representation pressure cannot upgrade claims")
    if payload.get("selected_as_current_target") is not False:
        raise ValueError("deferred QM pressure cannot replace the active target")
    if len(payload.get("literature_locators", [])) != 4:
        raise ValueError("expected four supplied literature locators")
    canonical_json_bytes(payload)


def validate_guardrail_payload(payload: dict[str, Any]) -> None:
    required_interface = {
        "question",
        "inputs",
        "equation_surfaces",
        "assumptions",
        "units",
        "allowed_operations",
        "forbidden_claims",
        "success_criteria",
        "failure_criteria",
        "outputs",
        "claim_ceiling",
        "reproduction_command",
    }
    if not required_interface.issubset(payload):
        raise ValueError("guardrail is missing required sprint interface fields")
    if payload.get("selected_next_target") != EXECUTION_TARGET:
        raise ValueError("guardrail does not select the bounded execution target")
    if payload["claim_ceiling"].get("claim_ladder_level") != 3:
        raise ValueError("claim ceiling must remain Level 3")
    if payload["inputs"].get("off_shell_exact_coefficient") != 0.84:
        raise ValueError("off-shell coefficient differs from frozen value")
    if payload["equation_surfaces"].get("equation_compendium_edited") is not False:
        raise ValueError("guardrail cannot edit the equation compendium")
    canonical_json_bytes(payload)


def build_execution_report() -> dict[str, Any]:
    result = json.loads(CALCULATION_OUTPUT_PATH.read_text(encoding="utf-8"))
    manifest = json.loads(CALCULATION_MANIFEST_PATH.read_text(encoding="utf-8"))
    if result.get("all_thresholds_passed") is not True:
        raise ValueError("calculation thresholds did not pass")
    if not all(result.get("threshold_checks", {}).values()):
        raise ValueError("one or more threshold checks are false")
    output_sha256 = sha256_path(CALCULATION_OUTPUT_PATH)
    if manifest.get("output_sha256") != output_sha256:
        raise ValueError("manifest output hash differs")
    geometry = result["background_geometry"]
    if geometry.get("background_geometry_classification") != (
        "locally_flat_nontrivial_conformal_connection"
    ):
        raise ValueError("background geometry classification differs")
    if geometry.get("scalar_curvature") != 0.0:
        raise ValueError("execution background is not scalar-flat")
    return {
        "schema_id": (
            "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_"
            "BACKGROUND_CALCULATION_EXECUTION_20260709_v0"
        ),
        "calculation_id": result["calculation_id"],
        "status": "executed_pending_result_review",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": EXECUTION_TARGET,
        "consumed_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_conformal_"
            "background_calculation_execution"
        ),
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_conformal_"
            "background_calculation_result_review"
        ),
        "packet_result": EXECUTION_OUTCOME,
        "strict_packet_result": EXECUTION_STRICT_OUTCOME,
        "calculation_output_path": (
            "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
            "IDENTITY-CONFORMAL-BACKGROUND-v0.json"
        ),
        "calculation_output_sha256": output_sha256,
        "calculation_manifest_path": (
            "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-"
            "IDENTITY-CONFORMAL-BACKGROUND-MANIFEST-v0.json"
        ),
        "calculation_manifest_sha256": sha256_path(CALCULATION_MANIFEST_PATH),
        "guardrail_sha256": manifest["guardrail_sha256"],
        "script_sha256": manifest["script_sha256"],
        "canonical_json_contract": manifest["canonical_json_contract"],
        "background_geometry_classification": geometry[
            "background_geometry_classification"
        ],
        "scalar_curvature": geometry["scalar_curvature"],
        "curvature_test_claimed": False,
        "covariant_connection_test_claimed": True,
        "control_counts": {
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
        "threshold_evidence": result["threshold_evidence"],
        "threshold_checks": result["threshold_checks"],
        "all_thresholds_passed": True,
        "naive_partial_divergence_negative_control": result[
            "naive_partial_divergence_negative_control"
        ],
        "claim": {
            "primary_label": "E-REPRO",
            "claim_status": "generated_pending_result_review",
            "claim_ceiling_level": 3,
            "claim_scope": (
                "locally-flat conformal-coordinate scalar connection-covariance "
                "calculation only"
            ),
        },
        "proposed_equation_id_pending_review": result[
            "proposed_equation_id_pending_review"
        ],
        "equation_compendium_edited": False,
        "recommended_post_review_target": result[
            "recommended_post_review_target"
        ],
        "boundary": result["boundary"],
        "ccft_lane_status": "paused_upstream_prerequisites",
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def _reject_nonfinite_json(token: str) -> None:
    raise ValueError(f"non-finite JSON token: {token}")


def _load_strict_json(path: Path) -> dict[str, Any]:
    payload = json.loads(
        path.read_text(encoding="utf-8"),
        parse_constant=_reject_nonfinite_json,
    )
    if not isinstance(payload, dict):
        raise ValueError("top-level JSON value must be an object")
    return payload


def verify_calculation_result(
    *,
    guardrail_path: Path = GUARDRAIL_REPORT_PATH,
    script_path: Path = CALCULATION_SCRIPT_PATH,
    output_path: Path = CALCULATION_OUTPUT_PATH,
    manifest_path: Path = CALCULATION_MANIFEST_PATH,
    execution_report_path: Path = EXECUTION_REPORT_PATH,
) -> dict[str, Any]:
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

    result: dict[str, Any] | None = None
    manifest: dict[str, Any] | None = None
    execution_report: dict[str, Any] | None = None
    try:
        result = _load_strict_json(output_path)
        manifest = _load_strict_json(manifest_path)
        execution_report = _load_strict_json(execution_report_path)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError):
        mismatch_codes.append("schema_mismatch")

    canonical_bytes_match = False
    independent_regeneration_match = False
    geometry_match = False
    threshold_match = False
    negative_control_match = False
    per_resolution_results_match = False
    if result is not None and manifest is not None:
        try:
            canonical_bytes_match = (
                output_path.read_bytes() == calculation_canonical_json_bytes(result)
                and manifest_path.read_bytes()
                == calculation_canonical_json_bytes(manifest)
            )
        except (TypeError, ValueError):
            canonical_bytes_match = False
        if not canonical_bytes_match:
            mismatch_codes.append("canonicalization_mismatch")

        required_result_fields = {
            "schema_id",
            "calculation_id",
            "background_geometry",
            "parameters",
            "on_shell",
            "off_shell",
            "naive_partial_divergence_negative_control",
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
            "scalar_curvature",
            "curvature_test_claimed",
            "covariant_connection_test_claimed",
            "result_review_target",
        }
        if (
            not required_result_fields.issubset(result)
            or not required_manifest_fields.issubset(manifest)
            or result.get("calculation_id") != CALCULATION_ID
            or manifest.get("calculation_id") != CALCULATION_ID
        ):
            mismatch_codes.append("schema_mismatch")

        try:
            per_resolution_results_match = (
                result["parameters"]["time_slices_eta"] == list(TIME_SLICES)
                and result["parameters"]["resolutions_N"] == list(RESOLUTIONS)
                and len(result["on_shell"]["time_slice_results"]) == 12
                and len(result["off_shell"]["time_slice_results"]) == 12
                and len(result["on_shell"]["resolution_aggregates"]) == 4
                and len(result["off_shell"]["resolution_aggregates"]) == 4
                and all(
                    len(control["time_slice_results"])
                    == len(TIME_SLICES) * len(RESOLUTIONS)
                    for control in (result["on_shell"], result["off_shell"])
                )
            )
        except (KeyError, TypeError):
            per_resolution_results_match = False
        if not per_resolution_results_match:
            mismatch_codes.append("count_mismatch")

        geometry = result.get("background_geometry", {})
        geometry_match = (
            geometry.get("background_geometry_classification")
            == "locally_flat_nontrivial_conformal_connection"
            and geometry.get("scalar_curvature") == 0.0
            and geometry.get("riemann_tensor_max_absolute_component") == 0.0
            and geometry.get("nonzero_connection_component_count") == 4
            and geometry.get("curvature_test_claimed") is False
            and geometry.get("covariant_connection_test_claimed") is True
            and manifest.get("background_geometry_classification")
            == "locally_flat_nontrivial_conformal_connection"
            and manifest.get("scalar_curvature") == 0.0
            and manifest.get("curvature_test_claimed") is False
            and manifest.get("covariant_connection_test_claimed") is True
        )
        if not geometry_match:
            mismatch_codes.append("geometry_classification_mismatch")

        expected_check_keys = {
            "two_finest_convergence_order_at_least_1_8",
            "finest_combined_off_shell_relative_error_at_most_2_percent",
            "exact_coefficient_error_at_most_1e_12",
            "finest_off_shell_divergence_over_100_times_on_shell",
            "metric_compatibility_error_at_most_1e_12",
            "flat_limit_discrepancy_at_most_1e_12",
        }
        checks = result.get("threshold_checks", {})
        threshold_evidence = result.get("threshold_evidence", {})
        threshold_match = (
            result.get("all_thresholds_passed") is True
            and set(checks) == expected_check_keys
            and all(checks.values())
            and threshold_evidence.get("metric_compatibility_max_absolute_error")
            == 0.0
            and threshold_evidence.get("flat_limit_max_absolute_discrepancy")
            == 0.0
            and result.get("claim", {}).get("primary_label") == "E-REPRO"
            and result.get("claim", {}).get("claim_ceiling_level") == 3
        )
        if not threshold_match:
            mismatch_codes.append("threshold_mismatch")

        negative_control = result.get(
            "naive_partial_divergence_negative_control", {}
        )
        negative_control_match = (
            negative_control.get("failure_detected") is True
            and negative_control.get(
                "finest_on_shell_naive_to_covariant_error_ratio", 0.0
            )
            > 100.0
            and negative_control.get(
                "diagnostic_only_not_guardrail_threshold"
            )
            is True
        )
        if not negative_control_match:
            mismatch_codes.append("negative_control_mismatch")

        if (
            manifest.get("guardrail_sha256") != actual_hashes["guardrail_sha256"]
            or manifest.get("script_sha256") != actual_hashes["script_sha256"]
            or manifest.get("output_sha256") != actual_hashes["output_sha256"]
        ):
            mismatch_codes.append("manifest_hash_mismatch")

        fresh_result = rebuild_calculation_result()
        independent_regeneration_match = (
            calculation_canonical_json_bytes(fresh_result)
            == output_path.read_bytes()
        )
        if not independent_regeneration_match:
            mismatch_codes.append("regeneration_mismatch")

    if execution_report is not None:
        if (
            execution_report.get("calculation_output_sha256")
            != actual_hashes["output_sha256"]
            or execution_report.get("calculation_manifest_sha256")
            != actual_hashes["manifest_sha256"]
            or execution_report.get("all_thresholds_passed") is not True
            or execution_report.get("background_geometry_classification")
            != "locally_flat_nontrivial_conformal_connection"
            or execution_report.get("scalar_curvature") != 0.0
            or execution_report.get("curvature_test_claimed") is not False
            or execution_report.get("covariant_connection_test_claimed") is not True
        ):
            mismatch_codes.append("schema_mismatch")

    mismatch_codes = list(dict.fromkeys(mismatch_codes))
    accepted = not mismatch_codes
    threshold_evidence = result.get("threshold_evidence", {}) if result else {}
    negative_control_evidence = (
        result.get("naive_partial_divergence_negative_control", {})
        if result
        else {}
    )
    return {
        "accepted": accepted,
        "primary_claim_label": "E-REPRO" if accepted else "B-BLOCKED",
        "claim_status": (
            "accepted_scoped_level_3_locally_flat_connection_test_only"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "mismatch_codes": mismatch_codes,
        "expected_hashes": EXPECTED_EXECUTION_HASHES,
        "actual_hashes": actual_hashes,
        "canonical_bytes_match": canonical_bytes_match,
        "independent_in_memory_regeneration_match": independent_regeneration_match,
        "per_resolution_results_match": per_resolution_results_match,
        "background_geometry_classification_match": geometry_match,
        "all_six_thresholds_match": threshold_match,
        "naive_partial_divergence_negative_control_match": negative_control_match,
        "threshold_evidence": threshold_evidence,
        "naive_partial_divergence_negative_control": negative_control_evidence,
        "control_counts": {
            "time_slice_count": len(TIME_SLICES),
            "resolution_count": len(RESOLUTIONS),
            "on_shell_time_resolution_rows": len(TIME_SLICES) * len(RESOLUTIONS),
            "off_shell_time_resolution_rows": len(TIME_SLICES) * len(RESOLUTIONS),
            "on_shell_resolution_aggregates": len(RESOLUTIONS),
            "off_shell_resolution_aggregates": len(RESOLUTIONS),
            "divergence_component_count": 2,
        },
        "selected_next_target": (
            NONZERO_CURVATURE_GUARDRAIL_TARGET
            if accepted
            else REPRODUCIBILITY_REPAIR_TARGET
        ),
    }


def build_review_report(**verification_paths: Path) -> dict[str, Any]:
    verification = verify_calculation_result(**verification_paths)
    accepted = verification["accepted"]
    return {
        "schema_id": (
            "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_"
            "BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0"
        ),
        "review_id": (
            "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_"
            "BACKGROUND_CALCULATION_RESULT_REVIEW_v0"
        ),
        "status": (
            "accepted_scoped_e_repro"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": REVIEW_TARGET,
        "consumed_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_conformal_"
            "background_calculation_result_review"
        ),
        "selected_next_target": verification["selected_next_target"],
        "selected_next_target_kind": (
            "scalar_stress_energy_covariant_divergence_identity_nonzero_"
            "curvature_background_guardrail_packet"
            if accepted
            else "conformal_background_calculation_reproducibility_repair"
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
                "locally_flat_nontrivial_conformal_connection"
            ),
            "scalar_curvature": 0.0,
            "curvature_test_claimed": False,
            "covariant_connection_test_claimed": True,
        },
        "claim": {
            "primary_label": verification["primary_claim_label"],
            "claim_status": verification["claim_status"],
            "claim_ceiling_level": 3,
            "claim_scope": (
                "locally-flat conformal-coordinate scalar covariant-connection "
                "identity calculation only"
            ),
        },
        "execution_artifacts_modified_by_review": False,
        "equation_compendium_rows_activated": (
            [PROPOSED_EQUATION_ID] if accepted else []
        ),
        "equation_compendium_status": (
            "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"
            if accepted
            else "not_activated"
        ),
        "ccft_lane_status": "paused_upstream_prerequisites",
        "remaining_blockers": [
            "no genuine nonzero-curvature fixed-background witness",
            "no dynamical gravity or Einstein-scalar evolution",
            "no GR source admissibility",
            "no Bianchi compatibility",
            "no QFT-GR seam admissibility or closure",
            "no master-action promotion",
        ],
        "boundary": {
            "genuine_nonzero_curvature_validated": False,
            "gravity_dynamics_validated": False,
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
        description="Prepare the bounded curved-background scalar guardrail."
    )
    parser.add_argument("--out", type=Path, default=GUARDRAIL_REPORT_PATH)
    parser.add_argument("--qm-pressure-out", type=Path, default=QM_PRESSURE_PATH)
    args = parser.parse_args(argv)
    pressure = build_qm_representation_pressure()
    validate_qm_representation_pressure(pressure)
    payload = build_guardrail_payload(pressure)
    validate_guardrail_payload(payload)
    write_report(args.qm_pressure_out, pressure)
    write_report(args.out, payload)
    print(
        json.dumps(
            {
                "outcome": GUARDRAIL_OUTCOME,
                "qm_representation_pressure": "deferred_no_claim_upgrade",
                "selected_next_target": EXECUTION_TARGET,
            }
        )
    )
    return 0


def execution_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Record the conformal-background scalar execution."
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
                "output_sha256": payload["calculation_output_sha256"],
                "selected_next_target": REVIEW_TARGET,
            }
        )
    )
    return 0


def review_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Review the conformal-background scalar calculation result."
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
            }
        )
    )
    return 0 if payload["verification"]["accepted"] else 1
