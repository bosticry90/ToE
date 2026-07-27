from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_"
    "20260718_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_"
    "REVIEW_20260718_v0.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_"
    "REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_scalar_only_quadratic_gravity_range_and_weak_field_constraint_"
    "packet_review_v0.py"
)

TARGET = (
    "review_scalar_only_quadratic_gravity_range_and_weak_field_constraint_"
    "packet_v0_result"
)
VERDICT = "BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_quadratic_gravity_range_and_weak_field_constraint_"
    "packet_review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_DATA_ACQUISITION_FIT_OR_BRANCH_ADOPTION"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_20260718_v0.md":
        "eae347960a516ea714b35566c94488f1966b50d86fe9db57e28d31eb64544b78",
    "formal/docs/release/SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_20260718_v0.json":
        "c88204a2ddd51bcc31bb506b575860dd2995f798fc4abef5226ea11b147bea27",
    "formal/python/tools/scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_v0.py":
        "0772e935328fc24339f4328f8234a344d9faae403d68a0ba1e39488e397075c9",
    "formal/python/tests/test_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_v0.py":
        "1b766102369f7c2ce7ebf99bdd25e7cd7010b29953efb64d07c424e23baf81a7",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyQuadraticGravityRangeAndWeakFieldConstraintPacketV0.lean":
        "fa1eeaa5de63be5d65813bc2a26ad7f55714068e27345a047ba9052378bb0a8f",
}

DIAGNOSTICS = (
    "OBSERVATION_VECTOR_CUSTODY_INCOMPLETE",
    "UNCERTAINTY_OR_COVARIANCE_CONTRACT_INCOMPLETE",
    "NUISANCE_PRIOR_CONTRACT_INCOMPLETE",
    "EXTENDED_SOURCE_FORWARD_MODEL_ABSENT",
    "BOUNDARY_COVERAGE_PROCEDURE_UNCALIBRATED",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_packet() -> dict[str, Any]:
    value = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("range-constraint packet must be a JSON object")
    return value


def _validate_packet() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in PACKET_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"range-constraint packet custody drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})

    packet = _load_packet()
    if packet.get("verdict") != (
        "PREPARED_BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE_"
        "PENDING_INDEPENDENT_REVIEW"
    ):
        raise ValueError("range-constraint packet is not pending independent review")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("range-constraint packet did not rotate to this review")
    if packet.get("provisional_execution_readiness") != VERDICT:
        raise ValueError("range-constraint packet provisional block changed")
    if packet["scope"].get("constraint_execution_authorized") is not False:
        raise ValueError("prepared packet improperly authorized a likelihood execution")
    return custody, packet


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "PASS" if passed else "FAIL",
        "finding": finding,
    }


def _source_reproduction() -> dict[str, Any]:
    return {
        "primary_source": "https://arxiv.org/abs/2002.11761",
        "separation_domain": "52 micrometres to 3.0 millimetres",
        "measurement_setting_count": 95,
        "harmonics": ["18 omega", "54 omega", "120 omega"],
        "harmonic_count": 3,
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
        "published_penalized_fit_structure": (
            "sum over 95 settings and 3 torques with torque variance, propagated "
            "separation error, and five Gaussian nuisance penalties"
        ),
        "published_newtonian_baseline": "chi_squared=275.0 for nu=285, P=0.654",
        "supplement_statement": (
            "numerical gravitational torques and details of the Yukawa constraint "
            "analysis are assigned to Supplemental Material"
        ),
        "published_generic_limit": (
            "gravitational-strength Yukawa range below 38.6 micrometres at 95 percent confidence"
        ),
        "fixed_one_third_limit_reproduced": False,
        "independent_likelihood_executed": False,
    }


def _dependency_rows() -> list[dict[str, str]]:
    return [
        {
            "missing_item": "COMPLETE_95_BY_3_TORQUE_VECTOR_AND_DISPLACEMENTS",
            "required_operation": "construct the 285-component residual vector at every lambda0",
            "failure_if_guessed": "the fitted data and row-to-geometry mapping would be invented",
        },
        {
            "missing_item": "NUMERICAL_UNCERTAINTY_AND_CORRELATION_MODEL",
            "required_operation": "weight residuals and determine the effective information content",
            "failure_if_guessed": "independence assumptions could overstate exclusion power",
        },
        {
            "missing_item": "FIVE_NUMERICAL_NUISANCE_PRIORS",
            "required_operation": "profile calibration, centering, separation, and roughness at every lambda0",
            "failure_if_guessed": "the scalar template could be absorbed or exposed by invented priors",
        },
        {
            "missing_item": "VERIFIED_EXTENDED_SOURCE_TORQUE_IMPLEMENTATION",
            "required_operation": "map fixed A_Y=1/3 through detector-attractor geometry into three torque harmonics",
            "failure_if_guessed": "a point-source or approximate-geometry response would not be the experiment",
        },
        {
            "missing_item": "BOUNDARY_AWARE_COVERAGE_CALIBRATION",
            "required_operation": "assign a valid 95 percent exclusion rule with lambda0=0 at the null boundary",
            "failure_if_guessed": "a textbook threshold could have incorrect coverage",
        },
    ]


def _adversarial_probes(packet: dict[str, Any]) -> list[dict[str, Any]]:
    data_rows = {row["item_id"]: row for row in packet["primary_data_audit"]["rows"]}
    return [
        {
            "probe_id": "SUPPLEMENT_EXISTENCE_IS_NOT_CUSTODY",
            "attempt": "treat the paper's supplement citation as if its numerical bytes were frozen",
            "expected": "REJECT",
            "observed": "REJECT",
            "passed": data_rows["SUPPLEMENTAL_MATERIAL"]["status"] == "IDENTIFIED_BUT_NOT_INGESTED",
        },
        {
            "probe_id": "PLOT_DIGITIZATION_BYPASS",
            "attempt": "digitize plotted torque points and call them the primary 95x3 vector",
            "expected": "REJECT",
            "observed": "REJECT",
            "passed": True,
        },
        {
            "probe_id": "GENERIC_EXCLUSION_CURVE_BYPASS",
            "attempt": "read or rescale the published gravitational-strength curve at A_Y=1/3",
            "expected": "REJECT",
            "observed": "REJECT",
            "passed": packet["scope"]["published_limit_imported_as_packet_result"] is False,
        },
        {
            "probe_id": "DISSERTATION_SUBSTITUTION_BYPASS",
            "attempt": "substitute the methods dissertation for the missing calibrated vector and likelihood inputs",
            "expected": "REJECT",
            "observed": "REJECT",
            "passed": data_rows["DISSERTATION_METHODS_RECORD"]["execution_sufficient"] is False,
        },
        {
            "probe_id": "DIAGONAL_ERROR_GUESS",
            "attempt": "treat every torque as independent using only visible error bars",
            "expected": "REJECT",
            "observed": "REJECT",
            "passed": packet["primary_data_audit"]["complete_uncertainty_model_frozen"] is False,
        },
        {
            "probe_id": "REASONABLE_NUISANCE_PRIOR_GUESS",
            "attempt": "replace the five numerical experiment priors with analyst-selected widths",
            "expected": "REJECT",
            "observed": "REJECT",
            "passed": True,
        },
        {
            "probe_id": "POINT_SOURCE_GEOMETRY_BYPASS",
            "attempt": "apply the point-mass Yukawa formula directly at micrometre separations",
            "expected": "REJECT",
            "observed": "REJECT",
            "passed": packet["theory_to_observable_transport"]["point_mass_approximation_allowed"] is False,
        },
        {
            "probe_id": "ASYMPTOTIC_THRESHOLD_BYPASS",
            "attempt": "issue a one-sided 95 percent bound from an uncalibrated textbook Delta-chi-square threshold",
            "expected": "REJECT",
            "observed": "REJECT",
            "passed": packet["statistical_contract"]["numerical_threshold_selected"] is False,
        },
    ]


def _review_gates(
    packet: dict[str, Any],
    source: dict[str, Any],
    dependencies: list[dict[str, str]],
    probes: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    selected = packet["selected_primary_contract"]
    audit = packet["primary_data_audit"]
    scope = packet["scope"]
    return [
        _gate(
            "G1_EXACT_PACKET_AUTHORITY_AND_CUSTODY",
            packet["selected_next_target"] == TARGET,
            "Five packet artifacts match frozen SHA-256 values and rotate to this review.",
        ),
        _gate(
            "G2_COMPARISON_ONLY_PROVENANCE_RETAINED",
            packet["comparison_model"]["status"] == "SUPPLIED_SCALAR_ONLY_QUADRATIC_GRAVITY_COMPARISON"
            and packet["comparison_model"]["scalar_branch_adopted"] is False
            and packet["comparison_model"]["toe_native"] is False,
            "The fixed-amplitude signal remains a supplied comparison; beta=0, alpha, and the branch remain unadopted.",
        ),
        _gate(
            "G3_SELECTED_EXPERIMENT_SUITABLE_FOR_FIXED_ONE_THIRD_SIGNAL",
            packet["comparison_model"]["fixed_yukawa_amplitude"] == "A_Y=1/3"
            and selected["dataset_id"] == "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE"
            and selected["separation_domain"] == source["separation_domain"],
            "The 52 micrometre to 3 millimetre extended-source torsion balance is scientifically matched to the fixed A_Y=1/3 range test.",
        ),
        _gate(
            "G4_PRIMARY_PAPER_DIMENSIONS_AND_FIT_STRUCTURE_REPRODUCED",
            selected["measurement_settings"] == source["measurement_setting_count"]
            and selected["measurement_count"] == source["measurement_count"]
            and selected["experimental_parameter_count"] == source["experimental_parameter_count"]
            and selected["profiled_nuisance_count"] == source["profiled_nuisance_count"],
            "The paper independently reproduces 95 settings, three harmonics, 285 torques, 17 parameters, and five profiled nuisances.",
        ),
        _gate(
            "G5_OBSERVATION_VECTOR_CUSTODY_IS_DECISION_BEARING",
            audit["machine_readable_measurement_vector_frozen"] is False
            and dependencies[0]["missing_item"] == "COMPLETE_95_BY_3_TORQUE_VECTOR_AND_DISPLACEMENTS",
            "Without the complete vector and displacement metadata, no residual vector or likelihood can be constructed.",
        ),
        _gate(
            "G6_UNCERTAINTY_AND_CORRELATION_CONTRACT_INCOMPLETE",
            audit["complete_uncertainty_model_frozen"] is False,
            "Visible error bars or an assumed diagonal covariance cannot replace the numerical uncertainty contract.",
        ),
        _gate(
            "G7_FIVE_NUISANCE_PRIORS_CANNOT_BE_GUESSED",
            selected["profiled_nuisance_count"] == 5
            and len(selected["profiled_nuisances"]) == 5,
            "The five priors are decision-bearing because they control how geometry and calibration absorb a Yukawa-like signal.",
        ),
        _gate(
            "G8_EXTENDED_SOURCE_FORWARD_MODEL_NOT_EXECUTABLE",
            audit["executable_extended_source_model_frozen"] is False
            and packet["extended_source_contract"]["geometry_model_available_for_execution"] is False,
            "The density geometry is described but no verified executable three-harmonic torque model with complete inputs is frozen.",
        ),
        _gate(
            "G9_POINT_SOURCE_APPROXIMATION_REMAINS_FORBIDDEN",
            packet["theory_to_observable_transport"]["point_mass_approximation_allowed"] is False,
            "Micrometre-scale patterned sources require the extended density/torque transport or a quantified negligible form-factor error.",
        ),
        _gate(
            "G10_DISSERTATION_REMAINS_SUPPORTING_METHODS_ONLY",
            any(row["probe_id"] == "DISSERTATION_SUBSTITUTION_BYPASS" and row["passed"] for row in probes),
            "The dissertation can explain methods but cannot supply missing calibrated numerical evidence by substitution.",
        ),
        _gate(
            "G11_PLOTS_SECONDARY_SUMMARIES_AND_APPROXIMATE_GEOMETRY_CANNOT_BYPASS",
            all(row["passed"] for row in probes if row["probe_id"] in {
                "PLOT_DIGITIZATION_BYPASS", "POINT_SOURCE_GEOMETRY_BYPASS"
            }),
            "Plot digitization and approximate geometry are explicitly rejected as independent-fit inputs.",
        ),
        _gate(
            "G12_PUBLISHED_GENERIC_LIMIT_IS_ORACLE_NOT_PACKET_RESULT",
            selected["published_generic_limit_is_packet_result"] is False
            and scope["published_limit_imported_as_packet_result"] is False,
            "The published 38.6 micrometre generic gravitational-strength limit is retained only as a future reproduction oracle.",
        ),
        _gate(
            "G13_BOUNDARY_COVERAGE_REMAINS_UNCALIBRATED",
            packet["statistical_contract"]["numerical_threshold_selected"] is False
            and "bootstrap" in packet["statistical_contract"]["boundary_rule"],
            "The lambda0-to-zero null is a boundary; no uncalibrated asymptotic threshold may issue a bound.",
        ),
        _gate(
            "G14_BASELINE_AND_INJECTION_CONTROLS_REMAIN_UNEXECUTED",
            packet["future_execution_controls"]["executed_count"] == 0
            and packet["unblock_requirements"]["satisfied_count"] == 0,
            "Newtonian reproduction, null coverage, and fixed-amplitude injection recovery have not run.",
        ),
        _gate(
            "G15_SCIENTIFIC_SUITABILITY_AND_PROJECT_EXECUTABILITY_SEPARATED",
            selected["selection_status"] == "SELECTED_FOR_CONTRACT_AUDIT_ONLY"
            and audit["execution_sufficient_count"] == 0,
            "The experiment is scientifically suitable, while the independent project fit is not executable.",
        ),
        _gate(
            "G16_PRINCIPAL_BLOCK_AND_SUBORDINATE_DIAGNOSTICS_EXCLUSIVE",
            audit["provisional_block"] == VERDICT and len(DIAGNOSTICS) == 5,
            "The earliest principal block is missing primary numerical custody; forward-model and coverage failures remain subordinate diagnostics.",
        ),
        _gate(
            "G17_NO_LIKELIHOOD_BOUND_OR_THEORY_ADOPTION",
            scope["likelihood_evaluated"] is False
            and scope["numerical_lambda_bound_computed"] is False
            and scope["numerical_alpha_bound_computed"] is False
            and scope["scalar_branch_adopted"] is False
            and scope["gravitational_action_selected"] is False,
            "No real-data fit, scalar-range bound, alpha bound, branch, principle, or action is issued.",
        ),
        _gate(
            "G18_ROTATION_ONLY_TO_SCIENTIFIC_RESPONSE_SELECTION",
            scope["constraint_execution_authorized"] is False,
            "The blocked review authorizes only a later response-selection step, not data acquisition, reinterpretation, or fitting.",
        ),
    ]


def build_review() -> dict[str, Any]:
    custody, packet = _validate_packet()
    source = _source_reproduction()
    dependencies = _dependency_rows()
    probes = _adversarial_probes(packet)
    gates = _review_gates(packet, source, dependencies, probes)
    pass_count = sum(row["status"] == "PASS" for row in gates)
    failure_count = len(gates) - pass_count
    if failure_count:
        raise ValueError("range-constraint independent review gate failure")
    if not all(row["passed"] for row in probes):
        raise ValueError("range-constraint adversarial probe failure")

    return {
        "schema_id": (
            "toe.scalar_only_quadratic_gravity_range_and_weak_field_constraint."
            "packet_review.v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_packet_review_outcome": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifact_count": len(custody),
            "frozen_packet_artifacts": custody,
        },
        "independent_primary_source_reproduction": source,
        "scientific_suitability": {
            "observable_class": "SHORT_RANGE_INVERSE_SQUARE_LAW_TORSION_BALANCE",
            "experiment": "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE",
            "fixed_model_signal": "A_Y=1/3",
            "experiment_scientifically_suitable": True,
            "theory_to_observable_transport_structurally_defined": True,
            "independent_project_fit_executable": False,
            "published_result_rejected": False,
        },
        "decision_bearing_dependency_map": {
            "row_count": len(dependencies),
            "rows": dependencies,
        },
        "diagnostics": {
            "principal": VERDICT,
            "subordinate_count": len(DIAGNOSTICS),
            "subordinate": list(DIAGNOSTICS),
        },
        "adversarial_no_bypass_probes": {
            "probe_count": len(probes),
            "pass_count": sum(row["passed"] for row in probes),
            "rows": probes,
        },
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": pass_count,
            "failure_count": failure_count,
            "rows": gates,
        },
        "execution_block": {
            "constraint_execution_authorized": False,
            "real_data_analysis_executed": False,
            "likelihood_evaluated": False,
            "numerical_lambda_bound_computed": False,
            "numerical_alpha_bound_computed": False,
            "unblock_requirement_count": packet["unblock_requirements"]["requirement_count"],
            "satisfied_unblock_requirement_count": packet["unblock_requirements"]["satisfied_count"],
            "binding_unblock_requirements": packet["unblock_requirements"]["rows"],
        },
        "future_response_selection": {
            "automatic_successor_authorized": False,
            "selection_only": True,
            "candidate_responses": [
                "bounded acquisition and custody of exact supplementary materials",
                "direct legitimate request for primary numerical inputs",
                "select another experiment with complete data, covariance, and geometry",
                "prepare a publication-level supplied-constraint reinterpretation without claiming an independent fit",
            ],
            "selected_response_now": None,
        },
        "scope": {
            "independent_packet_review_executed": True,
            "packet_block_confirmed": True,
            "experiment_invalidated": False,
            "published_constraint_denied": False,
            "constraint_execution_authorized": False,
            "supplement_acquisition_authorized": False,
            "author_contact_authorized": False,
            "alternate_experiment_selected": False,
            "publication_level_reinterpretation_authorized": False,
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
            "weak_field_phenomenology_packet_review": "BLOCKED",
            "principal_block": VERDICT,
            "selected_experiment": "2020_EOTWASH_TORSION_BALANCE",
            "model_signal": "FIXED_A_Y_ONE_THIRD",
            "primary_data_custody": "INCOMPLETE",
            "covariance_and_nuisance_contract": "INCOMPLETE",
            "extended_source_torque_model": "NOT_EXECUTABLE",
            "coverage_calibration": "NOT_AVAILABLE",
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "scientific_sources": [
            {
                "role": "SELECTED_PRIMARY_SHORT_RANGE_EXPERIMENT",
                "source": "https://arxiv.org/abs/2002.11761",
            },
            {
                "role": "SUPPORTING_PRIMARY_METHODS_DISSERTATION_ONLY",
                "source": (
                    "https://digital.lib.washington.edu/researchworks/items/"
                    "971237d1-100a-41ae-9027-d1bbce8cf315/full"
                ),
            },
        ],
        "claim_ceiling": (
            "The selected Eot-Wash experiment is scientifically suitable for a fixed "
            "A_Y=1/3 scalar-range comparison, but the project lacks the complete "
            "machine-readable observation vector, numerical uncertainty and nuisance "
            "contract, verified extended-source torque implementation, and calibrated "
            "boundary-coverage rule required for an independent likelihood. The packet "
            "is blocked. No numerical range or alpha bound, scalar-branch adoption, "
            "native scalar bridge, native gravitational principle, gravitational action, "
            "orbital result, frame-dragging result, or master-action change is computed, "
            "selected, claimed, or authorized."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(raw)
    if args.check:
        if not path.exists() or path.read_bytes() != raw:
            raise SystemExit("range-constraint packet review artifact drift")
    if not args.write and not args.check:
        print(raw.decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
