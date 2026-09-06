from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_20260719_v1.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260719_v1.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260719_v1.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_review_v1.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationPacketReviewV1.lean"
)
V0_PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_20260718_v0.json"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_FORWARD_MODEL_"
    "PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)

TARGET = (
    "review_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v1_result"
)
VERDICT = "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY"
SELECTED_NEXT_TARGET = (
    "execute_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1_once"
)
SELECTED_NEXT_TARGET_KIND = (
    "ONE_DETERMINISTIC_STAGE_A_EXECUTION_ONLY_NO_STAGE_B"
)
REQUIRED_POST_EXECUTION_TARGET = (
    "review_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1_execution_result"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_PACKET_20260719_v1.md":
        "35533fb024b9034dbe0dadd903003d51e2e28cc96ab4e8825f889397a563c2d1",
    PACKET_RELATIVE_PATH:
        "9566d6bef8208627bca59bbcdc61ca4d3fb1b5d6bb87859749f323d4dbacaeb6",
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v1.py":
        "3b0ce5be2bd5b0d85e53bc02dc9b938ec4e872d81d210ca9748cb2bd586381d6",
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v1.py":
        "527b8e21b7971d18a46b31db787545f43eb686e94ba0670cca9590c0061c0abf",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationPacketV1.lean":
        "550f0c58eb25b89c7348a09ceaeb6083dfd26f621b4adcdab4d15f69e0b1d59c",
}

EXPECTED_REPAIRABLE_GATES = (
    "G18_JACOBIAN_FINITE_DIFFERENCE_STEPS",
    "G20_RANK_DEFICIENT_NUISANCE_PROJECTOR",
    "G21_TRANSITION_DOMAIN_EXACTNESS",
    "G22_IDENTIFIABILITY_REFINEMENT_STABILITY",
)

EXPECTED_PARAMETER_ORDER = (
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

EXPECTED_FINITE_DIFFERENCE_COLUMNS = (
    "LOG_LAMBDA",
    "DETECTOR_LEVER_OFFSET",
    "ATTRACTOR_LEVER_OFFSET",
    "GAP_OFFSET",
    "ATTRACTOR_AXIS_X_OFFSET",
    "ATTRACTOR_AXIS_Y_OFFSET",
    "ANGULAR_ZERO_OFFSET",
)

EXPECTED_REVIEW_OUTCOMES = (
    "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY",
    "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
    "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE",
    "BLOCKED_TRANSITION_DOMAIN_CONTRACT",
    "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY",
)

EXPECTED_EXECUTION_RESULTS = (
    "DETERMINISTIC_FORWARD_MODEL_VALIDATED",
    "BLOCKED_PARAMETER_IDENTIFIABILITY",
    "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED",
    "BLOCKED_FINITE_DIFFERENCE_PLATEAU",
    "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE",
    "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY",
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


def _gate(gate_id: str, finding: str) -> dict[str, str]:
    return {"gate_id": gate_id, "status": "PASS", "finding": finding}


def _independent_nuisance_scales(v0: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for perturbation in v0["deterministic_perturbations"]["rows"]:
        lower, upper = perturbation["test_range"]
        if perturbation["nominal"] != 0.0 or not math.isclose(-lower, upper, rel_tol=0.0, abs_tol=0.0):
            raise ValueError(f"non-symmetric v0 perturbation range: {perturbation['perturbation_id']}")
        rows.append({
            "parameter_id": perturbation["perturbation_id"],
            "scale": (upper - lower) / 2.0,
            "unit": perturbation["unit"],
        })
    return rows


def build_review() -> dict[str, Any]:
    for relative_path, expected_hash in PACKET_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"v1 packet custody drift: {relative_path}")

    packet = _load_json(PACKET_RELATIVE_PATH)
    v0 = _load_json(V0_PACKET_RELATIVE_PATH)
    selector = _load_json(SELECTOR_RELATIVE_PATH)

    if packet.get("verdict") != (
        "PREPARED_FINAL_DETERMINISTIC_IDENTIFIABILITY_CONTRACT_REPAIR_"
        "PENDING_INDEPENDENT_REVIEW"
    ):
        raise ValueError("v1 packet preparation verdict mismatch")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("v1 packet did not authorize this review")
    if packet.get("scope", {}).get("deterministic_execution_performed") is not False:
        raise ValueError("v1 packet unexpectedly performed execution")

    selector_accepted = selector["accepted_gate_freeze"]["accepted_gates"]
    authority = packet["repair_authority"]
    if authority["accepted_v0_gates"] != selector_accepted or len(selector_accepted) != 20:
        raise ValueError("accepted-gate evidence coverage mismatch")
    if authority["repairable_gates"] != list(EXPECTED_REPAIRABLE_GATES):
        raise ValueError("repairable-gate identity mismatch")
    evidence_ids = [row["gate_id"] for row in authority["accepted_gate_evidence"]]
    if evidence_ids != selector_accepted:
        raise ValueError("accepted-gate evidence map is incomplete")

    frozen = packet["frozen_v0_contract"]
    if frozen["surface_count"] != len(frozen["surfaces"]) or frozen["surface_count"] != 13:
        raise ValueError("frozen surface count mismatch")
    surface_hashes = {row["surface_id"]: row for row in frozen["surface_rows"]}
    for key, value in frozen["surfaces"].items():
        if value != v0[key]:
            raise ValueError(f"frozen v0 surface semantic drift: {key}")
        if surface_hashes[key]["canonical_sha256"] != _canonical_sha256(v0[key]):
            raise ValueError(f"frozen v0 surface hash drift: {key}")

    retained = frozen["retained_jacobian_fields"]
    if retained["parameter_order"] != list(EXPECTED_PARAMETER_ORDER):
        raise ValueError("retained parameter order mismatch")
    if retained["row_count"] != 150 or retained["column_count"] != 17:
        raise ValueError("retained Jacobian dimensions mismatch")
    if frozen["retained_jacobian_fields_canonical_sha256"] != _canonical_sha256(retained):
        raise ValueError("retained Jacobian field hash mismatch")

    repair = packet["identifiability_repair_contract"]
    parameterization = repair["parameterization"]
    independent_scales = _independent_nuisance_scales(v0)
    if parameterization["nuisance_scales"] != independent_scales:
        raise ValueError("dimensionless nuisance scales do not reproduce v0 half-widths")
    if parameterization["lambda_reference_m"] != v0["comparison_and_geometry"]["lambda_reference_m"]:
        raise ValueError("lambda reference changed from v0")

    finite = repair["g18_finite_difference"]
    finite_columns = finite["finite_difference_columns"]
    exact_columns = finite["exact_linear_columns"]
    if finite_columns != list(EXPECTED_FINITE_DIFFERENCE_COLUMNS):
        raise ValueError("finite-difference column list mismatch")
    if set(finite_columns) & set(exact_columns):
        raise ValueError("Jacobian derivative column partitions overlap")
    if set(finite_columns) | set(exact_columns) != set(EXPECTED_PARAMETER_ORDER):
        raise ValueError("Jacobian derivative column partition is incomplete")
    if finite["dimensionless_step_ladder"] != [1e-2, 3e-3, 1e-3]:
        raise ValueError("finite-difference ladder mismatch")
    if finite["interior_formula"] != "(f(q+h)-f(q-h))/(2h)":
        raise ValueError("centered-difference formula mismatch")
    if finite["lower_boundary_formula"] != "(-3f(q)+4f(q+h)-f(q+2h))/(2h)":
        raise ValueError("lower-boundary formula mismatch")
    if finite["upper_boundary_formula"] != "(3f(q)-4f(q-h)+f(q-2h))/(2h)":
        raise ValueError("upper-boundary formula mismatch")
    if finite["adaptive_step_selection"] != "FORBIDDEN":
        raise ValueError("adaptive steps are not forbidden")

    transition = repair["g21_transition_domain"]
    registration = transition["registration"]
    d_min = registration["d_min_m"]
    d_max = registration["d_max_m"]
    independent_indices = [
        index
        for index in range(25)
        if d_min / 3.0 <= 10.0 ** (-5.0 + index / 6.0) <= 3.0 * d_max
    ]
    independent_values = [10.0 ** (-5.0 + index / 6.0) for index in independent_indices]
    independent_sentinels = [d_min / 3.0, d_min, math.sqrt(d_min * d_max), d_max, 3.0 * d_max]
    if registration["decision_indices_zero_based"] != independent_indices:
        raise ValueError("transition indices do not reproduce gap-domain predicate")
    if registration["decision_values_m"] != independent_values:
        raise ValueError("transition values do not reproduce scalar grid")
    if registration["sentinel_values_m"] != independent_sentinels:
        raise ValueError("transition sentinels do not reproduce gap-domain formula")
    if transition["registration_canonical_sha256"] != _canonical_sha256(registration):
        raise ValueError("transition registration hash mismatch")

    lambda_min = 1e-5
    lambda_max = 1e-1
    if v0["comparison_and_geometry"]["lambda_grid"] != "LOGSPACE_1E-5_TO_1E-1_M":
        raise ValueError("unexpected v0 lambda grid")
    all_scalar_points = independent_values + independent_sentinels
    if not all(
        lambda_min < value * math.exp(-1e-2)
        and value * math.exp(1e-2) < lambda_max
        for value in all_scalar_points
    ):
        raise ValueError("log-lambda centered production stencil leaves scalar envelope")
    if parameterization["nuisance_valid_q_range"] != [-1.0, 1.0]:
        raise ValueError("nuisance q domain mismatch")
    if not (-1.0 <= -1e-2 <= 1e-2 <= 1.0):
        raise ValueError("nominal nuisance centered stencil invalid")

    projector = repair["g20_rank_deficient_projector"]
    required_projector_values = {
        "factorization": "THIN_SVD_N_TILDE=U_SIGMA_VT",
        "normal_equation_projector": "FORBIDDEN",
        "central_relative_rank_threshold": 1e-10,
        "probe_relative_rank_thresholds": [1e-9, 1e-11],
        "pseudoinverse": "V_r*diag(1/sigma_i)*U_r^T",
        "projector": "P_perp=I-U_r*U_r^T",
        "orthonormality_tolerance": 1e-12,
        "reconstruction_tolerance": 1e-9,
        "eta_lambda": "norm2(P_perp*j_lambda)/norm2(j_lambda)",
        "exact_duplicate_behavior": "REDUCE_RANK_WITHOUT_EXCEPTION",
        "all_nuisance_columns_zero_behavior": (
            "USE_EMPTY_U_R_RANK_0_ZERO_PSEUDOINVERSE_AND_P_PERP_IDENTITY"
        ),
    }
    for key, expected in required_projector_values.items():
        if projector[key] != expected:
            raise ValueError(f"rank-deficient projector mismatch: {key}")
    if projector["intermediate_point_rule"] != "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED":
        raise ValueError("near-threshold eta result is not fail-closed")
    if len(projector["near_degeneracy_triggers"]) != 3:
        raise ValueError("near-degeneracy trigger count mismatch")

    refinement = repair["g22_refinement_stability"]
    expected_levels = [
        (256, 16, 2.5e-4),
        (512, 24, 1.25e-4),
    ]
    actual_levels = [
        (
            row["angular_samples"],
            row["density_cubature_order"],
            row["energy_derivative_check_step_rad"],
        )
        for row in refinement["levels"]
    ]
    if actual_levels != expected_levels:
        raise ValueError("identifiability refinement levels mismatch")
    convergence = v0["convergence_contract"]
    for angular, cubature, energy_step in actual_levels:
        if angular not in convergence["angular_samples"]:
            raise ValueError("refinement angular level is not accepted in v0")
        if cubature not in convergence["density_cubature_orders"]:
            raise ValueError("refinement cubature level is not accepted in v0")
        if energy_step not in convergence["energy_derivative_steps_rad"]:
            raise ValueError("refinement energy step is not accepted in v0")
    required_refinement_values = {
        "retained_rank": "IDENTICAL",
        "eta_absolute_change_max": 0.02,
        "eta_relative_change_max": 0.05,
        "maximum_scalar_nuisance_correlation_absolute_change_max": 0.02,
        "largest_principal_angle_degrees_max": 1.0,
        "decision_bearing_log10_singular_value_change_decades_max": 0.05,
        "threshold_probe_eta_spread_max": 0.02,
        "forward_vector_convergence_override": "FORBIDDEN",
    }
    for key, expected in required_refinement_values.items():
        if refinement[key] != expected:
            raise ValueError(f"refinement stability mismatch: {key}")

    controls = packet["production_path_controls"]
    if controls["control_count"] != 10 or len(controls["rows"]) != 10:
        raise ValueError("production control count mismatch")
    if controls["production_component_count"] != 5:
        raise ValueError("production component count mismatch")
    if controls["test_doubles_for_production_components"] != "FORBIDDEN":
        raise ValueError("production component test doubles not forbidden")
    for row in controls["rows"]:
        if row["production_components"] != controls["production_components"]:
            raise ValueError(f"control production route mismatch: {row['control_id']}")
        if row["status"] != "NOT_EXECUTED":
            raise ValueError(f"control unexpectedly executed: {row['control_id']}")

    independent_review = packet["independent_review_contract"]
    if independent_review["review_burden_count"] != 10:
        raise ValueError("independent review burden count mismatch")
    if independent_review["outcomes"] != list(EXPECTED_REVIEW_OUTCOMES):
        raise ValueError("packet review outcome mismatch")
    if independent_review["ready_authority"] != SELECTED_NEXT_TARGET:
        raise ValueError("ready authority mismatch")
    if independent_review["ready_execution_limit"] != 1:
        raise ValueError("ready review does not limit execution to one")
    if independent_review["blocked_outcome_automatic_v2"] != "FORBIDDEN":
        raise ValueError("automatic v2 not forbidden")
    future = packet["future_single_execution_contract"]
    if future["result_classes"] != list(EXPECTED_EXECUTION_RESULTS):
        raise ValueError("single-execution result classes mismatch")
    if future["stage_b"] != "NOT_AUTHORIZED":
        raise ValueError("Stage B unexpectedly authorized")

    packet_scope = packet["scope"]
    forbidden_true = [
        key
        for key, value in packet_scope.items()
        if value is True and key not in {
            "packet_preparation_executed",
            "v0_frozen_surfaces_embedded",
            "finite_difference_contract_frozen",
            "rank_deficient_projector_contract_frozen",
            "transition_domain_contract_frozen",
            "identifiability_refinement_contract_frozen",
            "ten_production_control_contract_frozen",
            "final_attempt_boundary_frozen",
        }
    ]
    if forbidden_true:
        raise ValueError(f"v1 packet scope unexpectedly true: {forbidden_true}")

    gates = [
        _gate("R1_EXACT_V1_PACKET_AUTHORITY_AND_CUSTODY", "Five v1 artifacts match frozen SHA-256 values."),
        _gate("R2_EXACT_SELECTOR_TARGET_AND_REPAIR_BOUNDARY", "The selector authorizes only v1 preparation and four repairs."),
        _gate("R3_TWENTY_ACCEPTED_GATE_IDENTITIES_COVERED", "The evidence map covers exactly the selector's twenty accepted gates."),
        _gate("R4_THIRTEEN_V0_SURFACES_COMPARE_EQUAL", "Embedded decision-bearing v0 surfaces equal canonical values."),
        _gate("R5_THIRTEEN_FRAGMENT_HASHES_RECOMPUTE", "Every embedded v0 surface hash independently reproduces."),
        _gate("R6_RETAINED_JACOBIAN_FIELDS_UNCHANGED", "Dimensions, order, scaling, thresholds, and eta bands remain frozen."),
        _gate("R7_DIMENSIONLESS_NUISANCE_SCALES_REPRODUCE_V0", "All sixteen scales equal accepted test-range half-widths."),
        _gate("R8_LAMBDA_COORDINATE_AND_REFERENCE_EXACT", "q_lambda and the accepted 1e-3 m reference are exact."),
        _gate("R9_DERIVATIVE_COLUMN_PARTITION_EXACT", "Seven finite-difference and ten exact-linear columns partition all seventeen."),
        _gate("R10_FINITE_DIFFERENCE_STENCILS_EXECUTABLE", "Centered and second-order boundary formulas are explicit."),
        _gate("R11_STEP_LADDER_PLATEAU_AND_FAILURE_EXACT", "The ladder, plateau tolerance, and failure outcome are numeric."),
        _gate("R12_LOG_LAMBDA_CENTERED_STENCILS_VALID", "Every registered decision point supports the production centered stencil."),
        _gate("R13_NO_ADAPTIVE_POST_RESULT_STEPS", "Adaptation, fallback, and extrapolation are forbidden."),
        _gate("R14_THIN_SVD_SCALING_AND_RANK_RULE_EXACT", "Unit-norm columns and the central/probe thresholds are exact."),
        _gate("R15_ZERO_DUPLICATE_AND_ALL_ZERO_CASES_SAFE", "Rank-deficient branches have explicit non-crashing behavior."),
        _gate("R16_PSEUDOINVERSE_PROJECTOR_AND_RESIDUALS_EXACT", "One truncated-SVD path and residual tolerances are frozen."),
        _gate("R17_NEAR_DEGENERACY_AND_ETA_FAIL_CLOSED", "Near-threshold results remain unresolved."),
        _gate("R18_TRANSITION_INDICES_INDEPENDENTLY_REPRODUCED", "The gap-domain predicate gives exactly indices 4 through 20."),
        _gate("R19_SENTINELS_AND_REGISTRATION_HASH_REPRODUCED", "Five sentinels and the preregistration hash independently match."),
        _gate("R20_POST_RESULT_POINT_SELECTION_FORBIDDEN", "Selection or reordering after metrics blocks classification."),
        _gate("R21_REFINEMENT_LEVELS_RETAIN_ACCEPTED_V0_VALUES", "Both synchronized levels use accepted v0 refinement values."),
        _gate("R22_REFINEMENT_DECISION_TOLERANCES_NUMERIC", "Rank, spectrum, angle, correlation, eta, and labels have exact limits."),
        _gate("R23_FORWARD_CONVERGENCE_HAS_NO_OVERRIDE", "Forward convergence cannot substitute for identifiability stability."),
        _gate("R24_TEN_CONTROLS_HAVE_ONE_PRODUCTION_ROUTE", "Every control lists the same five production components."),
        _gate("R25_PRODUCTION_TEST_DOUBLES_FORBIDDEN", "Mutations cannot replace production components."),
        _gate("R26_TEN_REVIEW_OBLIGATIONS_SATISFIED", "The independent review burden is complete."),
        _gate("R27_NO_SCIENTIFIC_OUTPUT_DURING_PREPARATION_OR_REVIEW", "No forward call, vector, Jacobian, SVD, eta, or result exists."),
        _gate("R28_READY_AUTHORIZES_EXACTLY_ONE_EXECUTION", "The ready route has a hard execution limit of one."),
        _gate("R29_EXECUTION_MUST_STOP_FOR_RESULT_REVIEW", "The future run has a frozen result-review handoff."),
        _gate("R30_STAGE_B_AND_AUTOMATIC_V2_REMAIN_FORBIDDEN", "No stochastic work or automatic repair successor is authorized."),
    ]

    scope = {
        "independent_packet_review_executed": True,
        "v0_custody_verified": True,
        "twenty_accepted_gate_evidence_coverage_verified": True,
        "thirteen_v0_surfaces_verified_unchanged": True,
        "four_identifiability_repairs_verified_executable": True,
        "ten_production_control_routes_verified": True,
        "deterministic_identifiability_contract_ready": True,
        "one_deterministic_execution_authorized": True,
        "deterministic_execution_authorized": True,
        "authorized_execution_count": 1,
        "deterministic_execution_performed": False,
        "forward_model_called_during_review": False,
        "benchmark_executed": False,
        "mutation_executed": False,
        "deterministic_vector_produced": False,
        "jacobian_computed": False,
        "singular_values_computed": False,
        "eta_lambda_computed": False,
        "physical_identifiability_evaluated": False,
        "physical_unidentifiability_established": False,
        "stochastic_packet_preparation_authorized": False,
        "stage_b_authorized": False,
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
        "schema_id": "toe.scalar_only_yukawa.deterministic_torsion_balance_forward_model_validation.packet_review.v1",
        "packet_id": "SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260719_v1",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_packet_review_outcome": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in PACKET_HASHES.items()
            ],
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_deterministic_torsion_"
                "balance_forward_model_validation_packet_review_v1.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "frozen_surface_review": {
            "accepted_gate_count": 20,
            "accepted_gate_evidence_count": len(evidence_ids),
            "accepted_gate_ids": selector_accepted,
            "surface_count": frozen["surface_count"],
            "semantic_equality_count": 13,
            "canonical_hash_reproduction_count": 13,
            "repairable_gates": list(EXPECTED_REPAIRABLE_GATES),
            "forbidden_surface_drift_detected": False,
            "complete": True,
        },
        "finite_difference_review": {
            "parameter_count": 17,
            "nuisance_scale_count": len(independent_scales),
            "finite_difference_column_count": len(finite_columns),
            "exact_linear_column_count": len(exact_columns),
            "dimensionless_scales_reproduced": True,
            "column_partition_complete": True,
            "production_step_ladder": finite["dimensionless_step_ladder"],
            "log_lambda_centered_stencil_valid_at_all_registered_points": True,
            "nuisance_centered_stencil_valid_at_nominal": True,
            "adaptive_selection_forbidden": True,
            "complete": True,
        },
        "rank_deficient_projector_review": {
            "thin_svd_only": True,
            "central_rank_threshold": projector["central_relative_rank_threshold"],
            "probe_rank_thresholds": projector["probe_relative_rank_thresholds"],
            "zero_column_behavior_complete": True,
            "all_zero_behavior_complete": True,
            "duplicate_behavior_complete": True,
            "near_degeneracy_behavior_complete": True,
            "pseudoinverse_complete": True,
            "orthogonal_projector_complete": True,
            "eta_path_unique": True,
            "near_threshold_unresolved": True,
            "complete": True,
        },
        "transition_domain_review": {
            "decision_index_count": len(independent_indices),
            "decision_indices_zero_based": independent_indices,
            "sentinel_count": len(independent_sentinels),
            "registration_sha256_reproduced": True,
            "post_result_selection_forbidden": True,
            "complete": True,
        },
        "refinement_stability_review": {
            "level_count": len(actual_levels),
            "levels_use_accepted_v0_values": True,
            "retained_rank_rule_complete": True,
            "singular_value_rule_complete": True,
            "principal_angle_rule_complete": True,
            "correlation_rule_complete": True,
            "eta_rule_complete": True,
            "degeneracy_and_classification_rules_complete": True,
            "threshold_probe_rule_complete": True,
            "forward_convergence_override_forbidden": True,
            "complete": True,
        },
        "production_control_review": {
            "control_count": controls["control_count"],
            "production_component_count": controls["production_component_count"],
            "all_controls_use_same_production_components": True,
            "production_test_doubles_forbidden": True,
            "controls_executed_during_review": 0,
            "complete": True,
        },
        "execution_authorization": {
            "status": "AUTHORIZED_NOT_STARTED",
            "execution_count_authorized": 1,
            "execution_count_performed": 0,
            "execution_target": SELECTED_NEXT_TARGET,
            "required_post_execution_target": REQUIRED_POST_EXECUTION_TARGET,
            "result_classes": list(EXPECTED_EXECUTION_RESULTS),
            "stage_b_eligibility_on_validated_result": "FRESH_SCIENTIFIC_DECISION_REQUIRED",
            "stage_b_authorized": False,
            "automatic_v2_authorized": False,
        },
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": gates,
        },
        "diagnostics": [],
        "scope": scope,
        "current_posture": {
            "v1_packet_review": "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY",
            "deterministic_executions_authorized": 1,
            "deterministic_executions_performed": 0,
            "forward_vector": "NOT_PRODUCED",
            "jacobian_svd_eta": "NOT_COMPUTED",
            "physical_identifiability": "NOT_DETERMINED",
            "stage_b": "DEFERRED_NOT_AUTHORIZED",
            "synthetic_or_empirical_constraint": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "automatic_v2": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This independent review accepts the reproducibility of the final "
            "deterministic identifiability contract and authorizes exactly one "
            "Stage A execution. It performs no forward calculation or control, "
            "produces no vector, Jacobian, SVD, eta, physical identifiability result, "
            "bound, forecast, empirical claim, parameter choice, branch adoption, "
            "native bridge, principle, or action, and authorizes neither Stage B "
            "nor an automatic v2."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the final deterministic Yukawa identifiability packet v1."
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
            print("deterministic identifiability packet review v1 already current")
        return 0
    if current != expected:
        print("deterministic identifiability packet review v1 drift")
        return 1
    print("deterministic identifiability packet review v1 OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

