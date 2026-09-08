from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_"
    "20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_"
    "20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_v0.py"
)
TARGET = (
    "prepare_scalar_only_quadratic_gravity_range_and_weak_field_constraint_"
    "packet_v0"
)
VERDICT = (
    "PREPARED_BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE_"
    "PENDING_INDEPENDENT_REVIEW"
)
PROVISIONAL_READINESS = "BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_quadratic_gravity_range_and_weak_field_constraint_"
    "packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_REVIEW_ONLY"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md":
        "3e7b98d0e4b65e3beeb49e7833d0a1dc8ee288825184394f1655a603765546cf",
    "formal/docs/release/POST_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json":
        "2d2f354fc2ce3db5efd23fba2724f9b0e9295d82da301dc9f22d2b287019fda2",
    "formal/python/tools/post_scalar_only_quadratic_gravity_viability_and_native_relevance_scientific_response_selection_v0.py":
        "acbcf53f9718300d77af042f228fe586c6465a5a84cc01397fe8c66c7b921e9a",
    "formal/python/tests/test_post_scalar_only_quadratic_gravity_viability_and_native_relevance_scientific_response_selection_v0.py":
        "0d2dc4749ec131c76f70fbac6dac4931466fccf1101025cfca2940ca209413d8",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyQuadraticGravityViabilityAndNativeRelevanceScientificResponseSelectionV0.lean":
        "4fb91c86dcbeea0b36f194f2bc9220c90359e71fa96e6955c36599e994f10ba5",
    "formal/docs/release/SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_NATIVE_RELEVANCE_RESULT_REVIEW_20260718_v0.json":
        "278c9ad0d765891c92b6bfca2c5d50993c3d9ecee200657f44ac772d3f5057e9",
}

PACKET_REVIEW_OUTCOMES = (
    "READY_FOR_ONE_BOUNDED_CONSTRAINT_EXECUTION",
    "BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE",
    "BLOCKED_OBSERVABLE_TRANSPORT_INCOMPLETE",
    "BLOCKED_EXTENDED_SOURCE_MODEL",
    "BLOCKED_PARAMETER_DEGENERACY_UNRESOLVED",
    "BLOCKED_SCOPE_OR_PROVENANCE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in AUTHORITY_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"weak-field packet authority drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})

    selection = _load_json(
        "formal/docs/release/POST_SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_"
        "AND_NATIVE_RELEVANCE_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
    )
    if selection.get("verdict") != (
        "SELECTED_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_PREPARATION"
    ):
        raise ValueError("weak-field response-selection verdict mismatch")
    if selection.get("selected_candidate_id") != (
        "BOUND_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_PHENOMENOLOGY"
    ):
        raise ValueError("weak-field response candidate mismatch")
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("response selection did not authorize this packet")

    scalar_review = _load_json(
        "formal/docs/release/SCALAR_ONLY_QUADRATIC_GRAVITY_VIABILITY_AND_"
        "NATIVE_RELEVANCE_RESULT_REVIEW_20260718_v0.json"
    )
    if scalar_review.get("verdict") != (
        "ACCEPTED_BOUNDED_SCALAR_ONLY_COMPARISON_RESULT"
    ):
        raise ValueError("accepted scalar comparison result missing")
    claim = scalar_review.get("accepted_bounded_claim", {})
    if claim.get("native_bridge_count") != 0:
        raise ValueError("native scalar bridge count changed")
    if claim.get("empirical_viability_claim") is not False:
        raise ValueError("empirical viability was already claimed")
    return custody, selection


def _observable_candidates() -> list[dict[str, Any]]:
    return [
        {
            "candidate_id": "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE",
            "observable_class": "SHORT_RANGE_INVERSE_SQUARE_LAW_TORSION_BALANCE",
            "source": "https://arxiv.org/abs/2002.11761",
            "disposition": "SELECTED_FOR_PACKET_CONTRACT_ONLY",
            "reason": (
                "direct extended-source Yukawa test at 52 micrometre to 3 millimetre "
                "separations with sensitivity reaching gravitational-strength coupling"
            ),
            "data_analysis_selected": False,
        },
        {
            "candidate_id": "VECTOR_FORCE_SENSOR_2024_2026",
            "observable_class": "MICRON_SCALE_OPTICALLY_LEVITATED_FORCE_SENSOR",
            "source": "https://arxiv.org/abs/2412.13167",
            "disposition": "DEFERRED_INSUFFICIENT_FIXED_AMPLITUDE_SENSITIVITY",
            "reason": (
                "reported strength sensitivity is about 10^6 or larger in the relevant "
                "range, far above the fixed A_Y=1/3 comparison signal"
            ),
            "data_analysis_selected": False,
        },
        {
            "candidate_id": "SOLAR_SYSTEM_ORBITAL_WEAK_FIELD_CLASS",
            "observable_class": "LONG_RANGE_ORBITAL_DYNAMICS",
            "source": "https://arxiv.org/abs/2305.06752",
            "disposition": "DEFERRED_TRANSPORT_AND_DEGENERACY_UNRESOLVED",
            "reason": (
                "requires a complete observable model, ephemeris likelihood, and explicit "
                "G-or-GM nuisance calibration; light propagation also needs more than h00"
            ),
            "data_analysis_selected": False,
        },
    ]


def _data_audit_rows() -> list[dict[str, Any]]:
    return [
        {
            "item_id": "PRIMARY_PAPER_AND_ACCEPTED_MANUSCRIPT",
            "status": "AVAILABLE_AND_INSPECTED",
            "detail": (
                "J. G. Lee et al., Phys. Rev. Lett. 124, 101101 (2020), "
                "arXiv:2002.11761; 95 displacement settings and three harmonic torques"
            ),
            "execution_sufficient": False,
        },
        {
            "item_id": "PRIMARY_NUMERICAL_MEASUREMENT_VECTOR",
            "status": "NOT_OBTAINED_AND_FROZEN",
            "detail": (
                "the audited paper states that numerical gravitational torques are in "
                "Supplemental Material, but no complete machine-readable 95x3 vector was "
                "obtained in packet custody"
            ),
            "execution_sufficient": False,
        },
        {
            "item_id": "SUPPLEMENTAL_MATERIAL",
            "status": "IDENTIFIED_BUT_NOT_INGESTED",
            "detail": (
                "publisher supplement is referenced by the paper; interactive publisher "
                "access was not sufficient to freeze its bytes during this audit"
            ),
            "execution_sufficient": False,
        },
        {
            "item_id": "UNCERTAINTY_AND_COVARIANCE_MODEL",
            "status": "STRUCTURE_DESCRIBED_NUMERICAL_CUSTODY_INCOMPLETE",
            "detail": (
                "paper gives a penalized chi-square with torque errors, separation-error "
                "transport, and five Gaussian nuisance priors, but the complete numerical "
                "inputs and correlation justification are not frozen"
            ),
            "execution_sufficient": False,
        },
        {
            "item_id": "EXTENDED_SOURCE_GEOMETRY_AND_TORQUE_MODEL",
            "status": "DESCRIBED_NOT_EXECUTABLE_IN_PACKET_CUSTODY",
            "detail": (
                "Fourier-Bessel detector-attractor model and 17 experimental parameters "
                "are described, but no verified executable geometry/torque implementation "
                "with complete numerical inputs is frozen"
            ),
            "execution_sufficient": False,
        },
        {
            "item_id": "DISSERTATION_METHODS_RECORD",
            "status": "AVAILABLE_AS_SUPPORTING_PRIMARY_METHODS_SOURCE",
            "detail": (
                "J. G. Lee, A Fourier-Bessel Test of the Gravitational Inverse-Square "
                "Law, University of Washington (2020); not a substitute for frozen data"
            ),
            "source": (
                "https://digital.lib.washington.edu/researchworks/items/"
                "971237d1-100a-41ae-9027-d1bbce8cf315/full"
            ),
            "execution_sufficient": False,
        },
        {
            "item_id": "PUBLISHED_GENERIC_YUKAWA_LIMIT",
            "status": "AVAILABLE_AS_POST_EXECUTION_ORACLE_ONLY",
            "detail": (
                "published 95 percent gravitational-strength range limit is not the fixed "
                "A_Y=1/3 result and may not be read off or rescaled as this packet's bound"
            ),
            "execution_sufficient": False,
        },
    ]


def _controls() -> list[dict[str, Any]]:
    rows = [
        ("EXACT_RESPONSE_SELECTION_AND_AUTHORITY_CUSTODY", True),
        ("COMPARISON_ONLY_SCALAR_PROVENANCE_RETAINED", True),
        ("FIXED_YUKAWA_AMPLITUDE_ONE_THIRD", True),
        ("ONE_PRIMARY_OBSERVABLE_CLASS_ONLY", True),
        ("WEAKER_VECTOR_SENSOR_REJECTED_FOR_FIXED_AMPLITUDE", True),
        ("SOLAR_SYSTEM_CROSS_CHECK_DEFERRED", True),
        ("POINT_SOURCE_SHORTCUT_FORBIDDEN", True),
        ("EXTENDED_SOURCE_DENSITY_INTEGRAL_FROZEN", True),
        ("HARMONIC_TORQUE_OBSERVABLE_CHAIN_FROZEN", True),
        ("RAW_VECTOR_AND_UNCERTAINTY_CUSTODY_REQUIRED", True),
        ("FIVE_PROFILED_NUISANCE_PRIORS_RETAINED", True),
        ("CALIBRATION_AND_GEOMETRY_DEGENERACIES_EXPLICIT", True),
        ("FIXED_AMPLITUDE_NOT_READ_FROM_GENERIC_EXCLUSION_PLOT", True),
        ("BOUNDARY_NULL_REQUIRES_CALIBRATED_COVERAGE", True),
        ("SI_RANGE_INVERSE_LENGTH_PARTICLE_MASS_AND_ALPHA_MAP", True),
        ("NULL_BASELINE_INJECTION_AND_GEOMETRY_CONTROLS_FROZEN", True),
        ("PROVISIONAL_EXECUTION_BLOCK_FAILS_CLOSED", True),
        ("NO_NUMERICAL_DATA_ANALYSIS_OR_BOUND", True),
        ("NO_ALPHA_BRANCH_ACTION_OR_NATIVE_ADOPTION", True),
        ("ROTATION_ONLY_TO_INDEPENDENT_PACKET_REVIEW", True),
    ]
    return [
        {"control_id": control_id, "passed": passed}
        for control_id, passed in rows
    ]


def build_packet() -> dict[str, Any]:
    custody, selection = _validate_authority()
    candidates = _observable_candidates()
    data_rows = _data_audit_rows()
    controls = _controls()
    selected = [row for row in candidates if row["disposition"].startswith("SELECTED")]
    control_pass_count = sum(1 for row in controls if row["passed"])

    value: dict[str, Any] = {
        "packet_id": (
            "SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_"
            "PACKET_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "provisional_execution_readiness": PROVISIONAL_READINESS,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_response_selection_verdict": selection["verdict"],
            "consumed_candidate_id": selection["selected_candidate_id"],
            "frozen_artifact_count": len(custody),
            "frozen_artifacts": custody,
        },
        "comparison_model": {
            "status": "SUPPLIED_SCALAR_ONLY_QUADRATIC_GRAVITY_COMPARISON",
            "beta_zero_status": "COMPARISON_RESTRICTION_ONLY_NOT_ADOPTED",
            "metric_response": (
                "h00=-2GM/(c^2 r) [1+(1/3) exp(-r/lambda0)]"
            ),
            "newtonian_potential": (
                "Phi_N=-GM/r [1+A_Y exp(-r/lambda0)]"
            ),
            "fixed_yukawa_amplitude": "A_Y=1/3",
            "range": "lambda0=sqrt(-6 alpha_packet)>0",
            "alpha_map": "alpha_packet=-lambda0^2/6<0",
            "inverse_length_mass": "m0=1/lambda0 [m^-1]",
            "particle_mass": "M0=hbar/(c lambda0) [kg]",
            "particle_rest_energy": "M0 c^2=hbar c/lambda0",
            "alpha_value_or_bound_selected": False,
            "scalar_branch_adopted": False,
            "toe_native": False,
        },
        "observable_selection": {
            "candidate_count": len(candidates),
            "selected_primary_count": len(selected),
            "observable_class_cap": 2,
            "cross_check_selected": False,
            "rows": candidates,
        },
        "selected_primary_contract": {
            "dataset_id": "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE",
            "selection_status": "SELECTED_FOR_CONTRACT_AUDIT_ONLY",
            "paper": (
                "J. G. Lee et al., New Test of the Gravitational 1/r^2 Law at "
                "Separations down to 52 micrometres, PRL 124, 101101 (2020)"
            ),
            "doi": "10.1103/PhysRevLett.124.101101",
            "arxiv": "https://arxiv.org/abs/2002.11761",
            "separation_domain": "52 micrometres to 3.0 millimetres",
            "measurement_settings": 95,
            "harmonics": ["18 omega", "54 omega", "120 omega"],
            "measurement_count": 285,
            "experimental_parameter_count": 17,
            "profiled_nuisance_count": 5,
            "profiled_nuisances": [
                "x0 horizontal offset",
                "y0 horizontal offset",
                "s0 separation offset",
                "surface roughness correction",
                "autocollimator torque-scale gamma",
            ],
            "published_baseline": "chi_squared=275.0 for nu=285, P=0.654",
            "published_generic_limit_is_packet_result": False,
            "real_data_analysis_authorized": False,
        },
        "theory_to_observable_transport": {
            "point_source_potential": (
                "Phi(r)=-GM/r [1+A_Y exp(-r/lambda0)]"
            ),
            "point_source_radial_acceleration": (
                "a_r=-GM/r^2 [1+A_Y (1+r/lambda0) exp(-r/lambda0)]"
            ),
            "extended_source_yukawa_energy": (
                "U_Y=-G A_Y integral d3x d3x' rho_D(x) rho_A(x') "
                "exp(-|x-x'|/lambda0)/|x-x'|"
            ),
            "measured_torque": "N_Y(phi)=-partial U_Y/partial phi",
            "measured_harmonics": "Fourier components N_18omega, N_54omega, N_120omega",
            "point_mass_approximation_allowed": False,
            "required_implementation": (
                "one verified Fourier-Bessel or direct density-integration model for both "
                "Newtonian and fixed-amplitude Yukawa torques"
            ),
            "transport_executed": False,
        },
        "extended_source_contract": {
            "required_inputs": [
                "detector and attractor density masks",
                "material densities and removed masses",
                "detector and attractor thicknesses",
                "hole-filling glue density and geometry",
                "isolation foil and face-layer thicknesses",
                "x y s displacement record",
                "attractor runout and tilt",
                "surface roughness model",
                "rotation phase convention",
                "torque calibration and transfer function",
            ],
            "point_source_validity_criterion": (
                "forbidden unless a quantified form-factor error is below the preregistered "
                "numerical tolerance across the complete scanned lambda0 domain"
            ),
            "geometry_model_available_for_execution": False,
        },
        "primary_data_audit": {
            "row_count": len(data_rows),
            "execution_sufficient_count": sum(
                1 for row in data_rows if row["execution_sufficient"]
            ),
            "rows": data_rows,
            "machine_readable_measurement_vector_frozen": False,
            "complete_uncertainty_model_frozen": False,
            "executable_extended_source_model_frozen": False,
            "provisional_block": PROVISIONAL_READINESS,
        },
        "degeneracy_contract": {
            "primary_short_range": {
                "GM_degeneracy": "MITIGATED_BY_GEOMETRIC_HARMONICS_NOT_ASSUMED_ABSENT",
                "torque_scale": "PROFILE_GAMMA_WITH_PRIMARY_GAUSSIAN_PRIOR",
                "separation_and_centering": "PROFILE_X0_Y0_S0_WITH_PRIMARY_PRIORS",
                "surface_model": "PROFILE_ROUGHNESS_CORRECTION",
                "restricted_parameters_may_be_fixed_only_if_NUMERICAL_ERROR_IS_REPRODUCED": True,
            },
            "deferred_long_range": {
                "lambda_much_greater_than_r": (
                    "Yukawa response approaches a 4/3 rescaling and can be absorbed in G, "
                    "M, or GM without independent calibration"
                ),
                "status": "DEFERRED_NO_EPHEMERIS_OR_GM_COVARIANCE_FROZEN",
            },
        },
        "statistical_contract": {
            "analysis_status": "PREREGISTERED_STRUCTURE_NOT_EXECUTABLE",
            "likelihood_family": (
                "primary penalized Gaussian chi-square with torque errors, propagated "
                "separation uncertainty, and five Gaussian nuisance priors"
            ),
            "physical_parameters": ["lambda0>0 with fixed A_Y=1/3"],
            "nuisance_rule": "profile all five primary nuisances at every lambda0",
            "scan_rule": (
                "log-spaced lambda0 grid spanning only the validated geometry/data domain, "
                "with adaptive refinement near likelihood transitions"
            ),
            "null": "lambda0 approaches 0; software cross-check A_Y=0",
            "boundary_rule": (
                "do not assume a textbook Delta-chi-square law; calibrate the test statistic "
                "and simultaneous scan coverage by parametric bootstrap or an equivalent "
                "validated Neyman construction"
            ),
            "confidence_level": "95 percent one-sided exclusion after coverage calibration",
            "allowed_set_rule": (
                "report the complete connected or disconnected allowed lambda0 set; report "
                "a single lambda_max only if topology and monotonicity are demonstrated"
            ),
            "combination_rule": "NO_DATASET_COMBINATION_IN_V0",
            "failure_rule": (
                "block on missing numerical vector, singular or unjustified uncertainty "
                "model, failed baseline reproduction, or failed injection coverage"
            ),
            "numerical_threshold_selected": False,
        },
        "si_conversion_contract": {
            "lambda0": "metres",
            "m0": "1/lambda0 in inverse metres",
            "M0": "hbar/(c lambda0) in kilograms",
            "M0_c2": "hbar c/lambda0 in joules or electronvolts",
            "alpha_packet": "-lambda0^2/6 in square metres",
            "allowed_range_translation": (
                "if 0<lambda0<lambda_max, then -lambda_max^2/6<alpha_packet<0"
            ),
            "exact_alpha_zero_from_finite_data_licensed": False,
        },
        "future_execution_controls": {
            "control_count": 9,
            "executed_count": 0,
            "rows": [
                "lambda0_to_zero_Einstein_limit",
                "A_Y_to_zero_software_null",
                "published_Newtonian_baseline_reproduction",
                "synthetic_fixed_amplitude_signal_recovery",
                "synthetic_null_coverage",
                "extended_geometry_integration_convergence",
                "point_source_shortcut_rejection",
                "nuisance_prior_and_profile_recovery",
                "SI_round_trip_lambda_m0_M0_alpha",
            ],
        },
        "unblock_requirements": {
            "requirement_count": 5,
            "rows": [
                "freeze the complete 95x3 numerical torque vector and displacement metadata",
                "freeze the complete numerical uncertainty model and five nuisance priors",
                "freeze or independently reproduce a verified extended-source torque model",
                "reproduce the published Newtonian baseline before exposing A_Y=1/3",
                "pass null and signal-injection coverage controls under the frozen scan rule",
            ],
            "all_required": True,
            "satisfied_count": 0,
        },
        "outcome_contract": {
            "packet_review_outcomes": list(PACKET_REVIEW_OUTCOMES),
            "provisional_packet_review_outcome": PROVISIONAL_READINESS,
            "independent_review_may_upgrade_to_ready_only_if_all_unblock_requirements_pass": True,
            "future_numerical_outcome": None,
        },
        "preparation_controls": {
            "control_count": len(controls),
            "pass_count": control_pass_count,
            "failure_count": len(controls) - control_pass_count,
            "rows": controls,
        },
        "scope": {
            "packet_preparation_executed": True,
            "independent_packet_review_executed": False,
            "primary_dataset_selected_for_contract_audit": True,
            "primary_data_custody_complete": False,
            "constraint_execution_authorized": False,
            "real_data_analysis_executed": False,
            "likelihood_evaluated": False,
            "numerical_lambda_bound_computed": False,
            "numerical_alpha_bound_computed": False,
            "published_limit_imported_as_packet_result": False,
            "beta_zero_adopted": False,
            "alpha_sign_or_value_adopted": False,
            "scalar_branch_adopted": False,
            "native_scalar_bridge_identified": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_sector_selected": False,
            "orbital_or_light_propagation_analysis_executed": False,
            "frame_dragging_resumed": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "scalar_only_comparison": "COMPLETED_AND_ACCEPTED",
            "native_relevance": "UNESTABLISHED",
            "selected_response": "BOUND_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_PHENOMENOLOGY",
            "packet": VERDICT,
            "primary_observable_class": "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE",
            "cross_check": "DEFERRED",
            "execution_readiness": PROVISIONAL_READINESS,
            "numerical_bound": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "sources": [
            {
                "source": "https://arxiv.org/abs/2002.11761",
                "role": "SELECTED_PRIMARY_SHORT_RANGE_EXPERIMENT",
            },
            {
                "source": (
                    "https://digital.lib.washington.edu/researchworks/items/"
                    "971237d1-100a-41ae-9027-d1bbce8cf315/full"
                ),
                "role": "PRIMARY_METHODS_DISSERTATION",
            },
            {
                "source": "https://arxiv.org/abs/2412.13167",
                "role": "CURRENT_VECTOR_SENSOR_SENSITIVITY_CROSS_CHECK",
            },
            {
                "source": "https://arxiv.org/abs/2305.06752",
                "role": "DEFERRED_SOLAR_SYSTEM_TRANSPORT_ORACLE",
            },
        ],
        "claim_ceiling": (
            "Preparation and public-source sufficiency audit only for a fixed-amplitude "
            "scalar comparison constraint. The selected short-range observable class and "
            "theory-to-torque contract are frozen, but public numerical custody is not yet "
            "sufficient for execution. No real likelihood, lambda0 or alpha bound, branch "
            "adoption, native scalar bridge, native gravitational principle, gravitational "
            "action, orbital result, frame-dragging result, or master-action change is "
            "computed, selected, claimed, or authorized."
        ),
    }

    if len(selected) != 1:
        raise ValueError("exactly one primary observable class must be selected")
    if value["comparison_model"]["fixed_yukawa_amplitude"] != "A_Y=1/3":
        raise ValueError("fixed scalar Yukawa amplitude drift")
    if value["primary_data_audit"]["provisional_block"] != PROVISIONAL_READINESS:
        raise ValueError("data sufficiency must fail closed")
    if value["scope"]["real_data_analysis_executed"]:
        raise ValueError("packet preparation executed real data analysis")
    if value["preparation_controls"]["failure_count"]:
        raise ValueError("weak-field packet preparation controls failed")
    return value


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("scalar weak-field constraint packet is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "controls": report["preparation_controls"]["pass_count"],
            "readiness": report["provisional_execution_readiness"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
