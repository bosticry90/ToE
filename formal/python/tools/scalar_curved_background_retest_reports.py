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
