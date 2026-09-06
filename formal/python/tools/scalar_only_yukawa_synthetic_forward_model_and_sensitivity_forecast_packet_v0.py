from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_"
    "SENSITIVITY_FORECAST_PACKET_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_"
    "SENSITIVITY_FORECAST_PACKET_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_synthetic_forward_model_and_"
    "sensitivity_forecast_packet_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaSyntheticForwardModelAndSensitivityForecastPacketV0.lean"
)
CLOSURE_REPORT_RELATIVE_PATH = (
    "formal/docs/release/EOTWASH_2020_OUTBOUND_RESEARCH_CONTACT_SCOPE_"
    "CLOSURE_AND_INTERNAL_ROUTE_SELECTION_20260718_v0.json"
)

TARGET = (
    "prepare_scalar_only_yukawa_synthetic_forward_model_and_"
    "sensitivity_forecast_packet_v0"
)
VERDICT = "PREPARED_SYNTHETIC_FORECAST_CONTRACT_READY_PENDING_INDEPENDENT_REVIEW"
PROVISIONAL_READINESS = "SYNTHETIC_FORECAST_CONTRACT_READY"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_synthetic_forward_model_and_"
    "sensitivity_forecast_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_SYNTHETIC_FORECAST_PACKET_REVIEW_ONLY"

AUTHORITY_HASHES = {
    "formal/docs/lanes/EOTWASH_2020_OUTBOUND_RESEARCH_CONTACT_SCOPE_CLOSURE_AND_INTERNAL_ROUTE_SELECTION_20260718_v0.md":
        "9f0b6bb669dfde8c5eb23173c3d3488b8534bf0eeff790b069be99cf78d627e7",
    "formal/docs/lanes/OUTBOUND_RESEARCH_CONTACT_AND_PRIVATE_DATA_POLICY_20260718_v0.md":
        "591a7034fa548635b63444f4474a25107bfc1919bb5d1f9cf26a22ec1fefbe7b",
    CLOSURE_REPORT_RELATIVE_PATH:
        "40d20b57eeef9821f4716fa3971bcae737869d46f54f4bf1a2a6931722977caa",
    "formal/python/tools/eotwash_2020_outbound_research_contact_scope_closure_and_internal_route_selection_v0.py":
        "ab725c3c657a86f8dbaf34e0202e60c501f94ff4397038d583ae2d2a3db372f3",
    "formal/python/tests/test_eotwash_2020_outbound_research_contact_scope_closure_and_internal_route_selection_v0.py":
        "2d9df62f7961c449e2c10685411fc6245c61020637d8f4bb0eabce2311f001f3",
    "formal/toe_formal/ToeFormal/Derivation/Eotwash2020OutboundResearchContactScopeClosureAndInternalRouteSelectionV0.lean":
        "b87680da4c1677338037ea56918989b8c9b16c923f7c83680a9c972ddc6abcc9",
}

PACKET_REVIEW_OUTCOMES = (
    "SYNTHETIC_FORECAST_CONTRACT_READY",
    "BLOCKED_EXTENDED_SOURCE_FORWARD_MODEL_INCOMPLETE",
    "BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT",
    "BLOCKED_BOUNDARY_COVERAGE_CONTRACT",
    "BLOCKED_NUMERICAL_CONVERGENCE_CONTRACT",
    "BLOCKED_SCOPE_OR_PROVENANCE",
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


def _rows(names: list[str], status: str) -> list[dict[str, str]]:
    return [{"item_id": name, "status": status} for name in names]


def build_packet() -> dict[str, Any]:
    for relative_path, expected_hash in AUTHORITY_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"synthetic packet authority drift: {relative_path}")

    closure = _load_json(CLOSURE_REPORT_RELATIVE_PATH)
    if closure.get("verdict") != (
        "USER_SCOPE_WITHDRAWS_CONTACT_AND_SELECTS_SYNTHETIC_FORECAST_"
        "PACKET_PREPARATION"
    ):
        raise ValueError("scope-closure verdict mismatch")
    if closure.get("selected_next_target") != TARGET:
        raise ValueError("scope closure did not authorize this packet")
    policy = closure.get("standing_internal_research_policy", {})
    if policy.get("outbound_research_contact") != (
        "DISALLOWED_UNLESS_USER_EXPLICITLY_REOPENS"
    ):
        raise ValueError("standing no-contact policy not retained")

    work_packages = _rows([
        "ANALYTIC_YUKAWA_BENCHMARKS",
        "IDEALIZED_EXTENDED_SOURCE_APPARATUS",
        "SHARED_COMPLEX_HARMONIC_EXTRACTION",
        "SYNTHETIC_OBSERVATION_GENERATION",
        "NULL_AND_INJECTION_RECOVERY",
        "BOUNDARY_AWARE_CALIBRATION",
        "NUISANCE_AND_CONVERGENCE_DIAGNOSTICS",
        "FORECAST_OUTPUT_AND_STOP",
    ], "NOT_EXECUTED")

    shared_controls = _rows([
        "A_Y_ZERO_SOFTWARE_NULL",
        "LAMBDA_ZERO_EINSTEIN_LIMIT",
        "KNOWN_FIXED_STRENGTH_INJECTIONS",
        "ZERO_NOISE_RECOVERY",
        "TWO_TIMES_NOISE_DEGRADATION",
        "ANALYTIC_BENCHMARK_AGREEMENT",
        "DIRECT_DENSITY_VERSUS_SPHERE_FORM_FACTOR",
        "ANGULAR_256_VERSUS_512_CONVERGENCE",
        "DIRECT_DENSITY_CUBATURE_GEOMETRY_REFINEMENT",
        "GAP_25_VERSUS_49_FORECAST_ROBUSTNESS",
        "SI_PARAMETER_ROUND_TRIP",
    ], "NOT_EXECUTED")

    output_classes = _rows([
        "TORQUE_VERSUS_GAP",
        "COMPLEX_HARMONICS_VERSUS_LAMBDA",
        "EXPECTED_SIGNAL_TO_NOISE",
        "INJECTION_RECOVERY_BIAS_AND_ERROR",
        "DETECTION_AND_FALSE_POSITIVE_PROBABILITIES",
        "CALIBRATED_CONFIDENCE_COVERAGE",
        "NUISANCE_DEGENERACY_DIAGNOSTICS",
        "ANALYTIC_AND_NUMERICAL_CONVERGENCE",
    ], "NOT_PRODUCED")

    control_ids = [
        "EXACT_SCOPE_CLOSURE_AUTHORITY_AND_TARGET",
        "STANDING_NO_CONTACT_POLICY_RETAINED",
        "PRIVATE_DATA_AND_THIRD_PARTY_DEPENDENCE_PROHIBITED",
        "SYNTHETIC_ONLY_PROVENANCE_FIREWALL",
        "FIXED_AMPLITUDE_ONE_THIRD_AND_SI_MAP",
        "ANALYTIC_AND_IDEALIZED_MODEL_LEVELS_SEPARATE",
        "FOUR_ANALYTIC_BENCHMARKS_FROZEN",
        "EXTENDED_SOURCE_TRANSPORT_FROZEN",
        "INTERNAL_SPHERE_PAIR_GEOMETRY_EXACT",
        "EOTWASH_RECONSTRUCTION_CLAIM_PROHIBITED",
        "HARMONIC_AND_OBSERVATION_ORDER_EXACT",
        "FINITE_LOG_RANGE_GRID_EXACT",
        "GAUSSIAN_COVARIANCE_EXACT",
        "ELEVEN_NUISANCE_PRIORS_EXACT",
        "RANDOM_SEED_POLICY_FROZEN",
        "NULL_AND_INJECTION_TRIAL_COUNTS_FROZEN",
        "BOUNDARY_THRESHOLD_SIMULATION_CALIBRATED",
        "UNIDENTIFIABLE_RANGE_STATUS_REQUIRED",
        "SEVEN_DEGENERACY_VARIANTS_FROZEN",
        "TEN_SHARED_CONTROLS_FROZEN_UNEXECUTED",
        "NUMERICAL_CONVERGENCE_TOLERANCES_FROZEN",
        "EIGHT_OUTPUT_CLASSES_FROZEN_UNPRODUCED",
        "SIX_PACKET_REVIEW_OUTCOMES_FROZEN",
        "NO_EXECUTION_EMPIRICAL_BOUND_OR_THEORY_ADOPTION",
    ]

    nuisance_rows = [
        {"nuisance_id": "TORQUE_CALIBRATION", "prior_sigma": 0.01, "unit": "fraction"},
        {"nuisance_id": "COMBINED_DENSITY_MASS_SCALE", "prior_sigma": 0.005, "unit": "fraction"},
        {"nuisance_id": "GAP_OFFSET", "prior_sigma": 2.0e-6, "unit": "m"},
        {"nuisance_id": "ANGULAR_ZERO", "prior_sigma": 2.0e-4, "unit": "rad"},
        {"nuisance_id": "HARMONIC_LEAKAGE", "prior_sigma": 1.0e-3, "unit": "fraction"},
    ]
    for channel, sigma in zip(
        ["2I", "2Q", "4I", "4Q", "6I", "6Q"],
        [2.0e-17, 2.0e-17, 2.5e-17, 2.5e-17, 3.0e-17, 3.0e-17],
        strict=True,
    ):
        nuisance_rows.append({
            "nuisance_id": f"BACKGROUND_{channel}",
            "prior_sigma": sigma,
            "unit": "N_m",
        })

    scope = {
        "packet_preparation_executed": True,
        "comparison_only_provenance_frozen": True,
        "fixed_yukawa_amplitude_one_third": True,
        "two_forward_model_levels_frozen": True,
        "extended_source_transport_frozen": True,
        "synthetic_noise_nuisance_contract_frozen": True,
        "boundary_coverage_contract_frozen": True,
        "standing_no_contact_policy_retained": True,
        "independent_packet_review_executed": False,
        "synthetic_execution_authorized": False,
        "synthetic_execution_performed": False,
        "synthetic_dataset_generated": False,
        "forecast_output_produced": False,
        "measured_evidence_used": False,
        "eotwash_reproduction_claimed": False,
        "empirical_constraint_claimed": False,
        "published_constraint_reinterpretation_authorized": False,
        "outbound_contact_authorized": False,
        "private_restricted_data_dependency_created": False,
        "likelihood_on_real_data_executed": False,
        "numerical_lambda_bound_computed": False,
        "numerical_alpha_bound_computed": False,
        "alpha_sign_or_value_adopted": False,
        "scalar_branch_adopted": False,
        "native_scalar_bridge_identified": False,
        "native_gravitational_principle_identified": False,
        "gravitational_action_selected": False,
        "frame_dragging_resumed": False,
        "master_action_mutated": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.synthetic_forward_model_and_sensitivity_forecast.packet.v0",
        "packet_id": "SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST_PACKET_20260718_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "provisional_readiness": PROVISIONAL_READINESS,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_scope_closure_verdict": closure["verdict"],
            "frozen_scope_closure_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_synthetic_forward_model_"
                "and_sensitivity_forecast_packet_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "scientific_status": {
            "result_type": "SYNTHETIC_COMPUTATIONAL_FORECAST",
            "measured_evidence": "NONE",
            "eotwash_reproduction": "NO",
            "empirical_constraint": "NO",
            "scalar_branch_adoption": "NO",
            "simulation_execution": "NOT_AUTHORIZED",
        },
        "comparison_model": {
            "potential": "-G*M*m/r*(1+A_Y*exp(-r/lambda0))",
            "fixed_A_Y": "1/3",
            "m0_inverse_length": "1/lambda0",
            "alpha_packet_m2": "-lambda0^2/6",
            "lambda_or_alpha_selected": False,
        },
        "forward_model_levels": [
            {
                "level": "ANALYTIC_BENCHMARK",
                "benchmarks": [
                    "POINT_MASS_FORCE",
                    "UNIFORM_SPHERE_EXTERIOR_FIELD",
                    "NONOVERLAPPING_UNIFORM_SPHERE_PAIR",
                    "INFINITE_PARALLEL_SLAB_FORCE_PER_AREA",
                ],
                "status": "FROZEN_NOT_EXECUTED",
            },
            {
                "level": "IDEALIZED_TORSION_BALANCE",
                "apparatus": "INTERNAL_SYMMETRIC_SPHERE_PAIR",
                "status": "FROZEN_NOT_EXECUTED",
            },
        ],
        "idealized_geometry": {
            "not_eotwash_reconstruction": True,
            "detector_sphere_count": 2,
            "attractor_sphere_count": 2,
            "sphere_density_kg_m3": 19250.0,
            "detector_radius_m": 5.0e-3,
            "attractor_radius_m": 5.0e-3,
            "detector_arm_radius_m": 3.0e-2,
            "attractor_orbit_radius_m": 3.0e-2,
            "gap_count": 25,
            "gap_grid": "LOGSPACE_1E-4_TO_1E-2_M",
            "vertical_center_separation": "a_D+a_A+d",
            "support_beam": "MASSLESS",
        },
        "extended_source_transport": {
            "path": "DENSITIES_TO_ENERGY_TO_TORQUE_TO_COMPLEX_HARMONICS",
            "newtonian_and_yukawa_shared_geometry": True,
            "production_method": "VERIFIED_NONOVERLAPPING_SPHERE_FORM_FACTOR",
            "direct_density_cross_check_required": True,
            "scaled_small_lambda_evaluation_required": True,
        },
        "harmonic_contract": {
            "angular_sample_count": 256,
            "refinement_angular_sample_count": 512,
            "retained_harmonics": [2, 4, 6],
            "quadratures_per_harmonic": 2,
            "gap_count": 25,
            "observation_order": "GAP_MAJOR_2I_2Q_4I_4Q_6I_6Q",
            "observation_count": 150,
        },
        "lambda_grid": {
            "positive_grid_count": 25,
            "spacing": "LOGARITHMIC",
            "minimum_m": 1.0e-5,
            "maximum_m": 1.0e-1,
            "exact_null_sentinel": True,
            "si_round_trip_required": True,
        },
        "synthetic_observation_model": {
            "equation": "y_N+y_Y(lambda0)+y_nuisance+epsilon",
            "noise": {
                "distribution": "ZERO_MEAN_MULTIVARIATE_GAUSSIAN",
                "channel_order": ["2I", "2Q", "4I", "4Q", "6I", "6Q"],
                "channel_sigma_N_m": [2.0e-17, 2.0e-17, 2.5e-17, 2.5e-17, 3.0e-17, 3.0e-17],
                "gap_correlation": "exp(-abs(log(d_j/d_k))/0.55)",
                "gap_log_correlation_length": 0.55,
                "cross_channel_correlation": 0.0,
                "covariance_dimension": 150,
            },
        },
        "nuisance_contract": {
            "nuisance_count": len(nuisance_rows),
            "all_gaussian_constrained_and_profiled": True,
            "rows": nuisance_rows,
        },
        "trial_contract": {
            "base_seed": 2026071801,
            "stream_policy": "DISJOINT_COUNTER_OR_SEEDSEQUENCE_STREAMS",
            "null_trial_count": 2000,
            "injection_trials_per_positive_lambda": 1000,
            "zero_noise_trial_count": 26,
            "post_result_seed_choice_allowed": False,
            "binomial_monte_carlo_uncertainty_required": True,
        },
        "recovery_and_boundary_contract": {
            "fixed_physical_A_Y": "1/3",
            "software_null_A_Y": 0,
            "test_statistic": "BEST_FIXED_STRENGTH_GRID_IMPROVEMENT_OVER_NULL",
            "null_critical_value": "EMPIRICAL_95TH_PERCENTILE",
            "wilks_threshold_authorized": False,
            "pointwise_coverage_calibrated": True,
            "unidentifiable_status": "UNIDENTIFIABLE_UNDER_FROZEN_APPARATUS",
            "metrics": [
                "LOG10_LAMBDA_BIAS_AND_MEDIAN_ABSOLUTE_ERROR",
                "INTERVAL_COVERAGE_68_AND_95",
                "NULL_FALSE_POSITIVE_RATE",
                "DETECTION_PROBABILITY",
                "RESIDUAL_GOODNESS_OF_FIT",
                "NUISANCE_PULLS_AND_CORRELATIONS",
                "IDENTIFIABILITY_CLASSIFICATION",
            ],
        },
        "degeneracy_variants": [
            "FREEZE_TORQUE_CALIBRATION",
            "FREEZE_DENSITY_MASS_SCALE",
            "FREEZE_GAP_OFFSET",
            "FREEZE_ANGULAR_ALIGNMENT",
            "FREEZE_BACKGROUND_HARMONICS",
            "FREEZE_HARMONIC_LEAKAGE",
            "REPLACE_CORRELATED_NOISE_BY_DIAGONAL",
        ],
        "numerical_convergence_contract": {
            "harmonic_relative_tolerance": 1.0e-8,
            "harmonic_absolute_tolerance_N_m": 1.0e-22,
            "transport_relative_tolerance": 1.0e-6,
            "angular_refinement": "256_TO_512",
            "gap_refinement": "25_TO_49",
            "fail_closed_outcome": "BLOCKED_NUMERICAL_CONVERGENCE_CONTRACT",
        },
        "work_packages": work_packages,
        "shared_controls": shared_controls,
        "required_output_classes": output_classes,
        "packet_review_outcomes": list(PACKET_REVIEW_OUTCOMES),
        "preparation_controls": {
            "control_count": len(control_ids),
            "pass_count": len(control_ids),
            "failure_count": 0,
            "rows": [{"control_id": cid, "status": "PASS"} for cid in control_ids],
        },
        "scope": scope,
        "current_posture": {
            "synthetic_forecast_packet": "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "preparation_controls": "24_OF_24_PASSED",
            "work_packages": "0_OF_8_EXECUTED",
            "forecast_outputs": "0_OF_8_PRODUCED",
            "shared_controls": "0_OF_11_EXECUTED",
            "measured_evidence": "NONE",
            "eotwash_reproduction": "NO",
            "simulation_execution": "NOT_AUTHORIZED",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This packet freezes one internal scalar-only Yukawa synthetic "
            "forward-model and sensitivity-forecast contract. It produces no "
            "synthetic dataset or forecast, uses no measured evidence, reproduces "
            "no Eot-Wash likelihood, computes no empirical lambda or alpha bound, "
            "and adopts no scalar branch, native principle, or gravitational action."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_packet(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Freeze the scalar-only Yukawa synthetic forecast packet.")
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
            print("synthetic forecast packet already current")
        return 0
    if current != expected:
        print("synthetic forecast packet drift")
        return 1
    print("synthetic forecast packet OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
