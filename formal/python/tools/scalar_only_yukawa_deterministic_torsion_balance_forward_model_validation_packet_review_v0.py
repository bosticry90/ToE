from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_20260718_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationPacketReviewV0.lean"
)

TARGET = (
    "review_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v0_result"
)
VERDICT = "BLOCKED_PARAMETER_IDENTIFIABILITY"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_deterministic_forward_model_"
    "packet_review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_PACKET_REPAIR_OR_DETERMINISTIC_EXECUTION"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_PACKET_20260718_v0.md":
        "29b6051dc6a0f880eab0bc4734e304f896b45d82aecd4aeda9e3246af05aabab",
    PACKET_RELATIVE_PATH:
        "ab5e555f857d883aa12346411d294f411b5228193f103d7dd91c4392fc66790e",
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v0.py":
        "ef7da3401505dc92072a6bdabbc6a52173d03f18a903c3d2c558e1a9f0d75f96",
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v0.py":
        "31bfb665c9004ea4de3ff5aeeb5eb3da98c1568fe6b9c5923b511fa6cdcf29f4",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationPacketV0.lean":
        "d63ac40f4aadf54e7703ae09143fa4a060b352fa4370a2030008622be9f603f7",
}

DIAGNOSTICS = (
    "JACOBIAN_FINITE_DIFFERENCE_BASE_STEPS_NOT_FROZEN",
    "RANK_DEFICIENT_NUISANCE_PROJECTOR_POLICY_INCOMPLETE",
    "TRANSITION_DOMAIN_NOT_EXACTLY_DEFINED",
    "IDENTIFIABILITY_REFINEMENT_ACCEPTANCE_TOLERANCES_INCOMPLETE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_packet() -> dict[str, Any]:
    value = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("deterministic packet must be a JSON object")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "finding": finding}


def build_review() -> dict[str, Any]:
    for relative_path, expected_hash in PACKET_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"deterministic packet custody drift: {relative_path}")

    packet = _load_packet()
    if packet.get("verdict") != (
        "PREPARED_DETERMINISTIC_FORWARD_MODEL_VALIDATION_CONTRACT_"
        "PENDING_INDEPENDENT_REVIEW"
    ):
        raise ValueError("deterministic packet is not pending independent review")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("deterministic packet did not rotate to this review")
    if packet.get("scope", {}).get("deterministic_execution_authorized") is not False:
        raise ValueError("packet improperly authorized deterministic execution")

    gates = [
        _gate("G1_EXACT_PACKET_AUTHORITY_AND_CUSTODY", True, "Five packet artifacts match frozen SHA-256 values."),
        _gate("G2_PENDING_REVIEW_STATUS_AND_NO_EXECUTION", True, "The packet is pending this review and executed no Stage A work."),
        _gate("G3_STAGE_A_ONLY_SCOPE", True, "Noise, covariance, Monte Carlo, likelihood, forecast, and Stage B remain excluded."),
        _gate("G4_FIXED_COMPARISON_AND_APPARATUS_GEOMETRY", True, "A_Y, SI constants, bodies, centers, gaps, and scalar-range grid are exact."),
        _gate("G5_HARMONIC_NORMALIZATION_PHASE_AND_SIGN", True, "Continuous and discrete coefficient definitions, angle, torque sign, and phase origin agree."),
        _gate("G6_REAL_150_VECTOR_ORDER_AND_UNITS", True, "25 gaps times three complex harmonics gives the exact gap-major real-150 N m vector."),
        _gate("G7_ONE_SHARED_PRODUCTION_FUNCTION_CHAIN", True, "Newtonian and Yukawa terms share distance, energy, torque, harmonic, and vector functions."),
        _gate("G8_UNIFORM_SPHERE_KERNEL_AND_STABLE_FORM_FACTOR", True, "The non-overlap form factor and scaled H representation are algebraically coherent."),
        _gate("G9_ANALYTIC_ENERGY_DERIVATIVE_TORQUE", True, "The frozen torque follows from -dU/dtheta with the stated pair-distance derivative."),
        _gate("G10_TWO_GENUINELY_INDEPENDENT_TORQUE_CHECKS", True, "Direct force/lever and five-point energy differentiation do not reuse the analytic torque."),
        _gate("G11_FOUR_BENCHMARKS_HAVE_EXACT_TARGETS", True, "Point, Yukawa, sphere, and apparatus checks have formulas or convergence targets."),
        _gate("G12_FIVE_SCIENTIFIC_MUTATIONS_ROUTE_TO_CONTROLS", True, "Sign, fixed amplitude, form factor, torque sign, and DFT normalization mutations are decision-bearing."),
        _gate("G13_SYMMETRY_PHASE_SWAP_AND_ZERO_CONTROLS", True, "Parity, periodicity, rigid shift, label swaps, and symmetry zeros follow from the frozen equal-pair geometry."),
        _gate("G14_NEAR_ZERO_ABSOLUTE_FLOOR", True, "Symmetry-protected channels use the frozen 1e-22 N m floor."),
        _gate("G15_SIXTEEN_PERTURBATION_MAPS_AND_ORDER", True, "Units, nominals, ranges, exact transformations, and composition order are frozen."),
        _gate("G16_EXPECTED_AMPLITUDE_DEGENERACY_DISCLOSED", True, "Calibration and the two density scales are correctly registered as one exact amplitude direction."),
        _gate("G17_JACOBIAN_DIMENSIONS_AND_PARAMETER_ORDER", True, "The real 150 by 17 surface and parameter order are exact."),
        _gate("G18_JACOBIAN_FINITE_DIFFERENCE_STEPS", False, "No numeric base-step table is assigned to log lambda and nonlinear geometry columns."),
        _gate("G19_DIMENSIONLESS_SVD_THRESHOLDS", True, "Column standardization intent, output scale, rank threshold, correlations, and eta thresholds are frozen."),
        _gate("G20_RANK_DEFICIENT_NUISANCE_PROJECTOR", False, "Projector construction, cutoff, zero-mode failures, and reconstruction tolerances are incomplete."),
        _gate("G21_TRANSITION_DOMAIN_EXACTNESS", False, "The five-contiguous-points rule refers to an undefined transition domain."),
        _gate("G22_IDENTIFIABILITY_REFINEMENT_STABILITY", False, "No numerical acceptance limits govern refined singular values, eta, rank, or classification changes."),
        _gate("G23_CANONICAL_SERIALIZATION_AND_DETERMINISM", True, "CSV, JSON, float format, ordering, hashing, and byte-repeat requirements are exact."),
        _gate("G24_STAGE_B_EMPIRICAL_AND_THEORY_FIREWALL", True, "No stochastic work, result, parameter choice, branch adoption, contact, or private data is authorized."),
    ]
    pass_count = sum(row["status"] == "PASS" for row in gates)

    unblock_text = [
        "freeze numeric base and half steps for log lambda and every nonlinear perturbation with domain behavior",
        "freeze parameter standardization and a rank-deficient nuisance projector algorithm cutoff reconstruction tolerance and condition-number rule",
        "define the transition domain by exact scalar-grid indices or a frozen mathematical predicate",
        "freeze quantitative refinement tolerances for singular values rank correlations eta projector residuals and classifications",
    ]

    scope = {
        "independent_packet_review_executed": True,
        "harmonic_and_real_150_contract_verified": True,
        "shared_kernel_and_torque_contract_verified": True,
        "benchmark_mutation_and_symmetry_contract_verified": True,
        "deterministic_perturbation_maps_verified": True,
        "exact_amplitude_degeneracy_verified": True,
        "packet_execution_ready": False,
        "packet_repair_authorized": False,
        "deterministic_execution_authorized": False,
        "deterministic_execution_performed": False,
        "benchmark_executed": False,
        "mutation_executed": False,
        "deterministic_vector_produced": False,
        "jacobian_computed": False,
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
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.deterministic_torsion_balance_forward_model_validation.packet_review.v0",
        "packet_id": "SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260718_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_packet_review_outcome": VERDICT,
        "execution_readiness": "NOT_READY",
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
                "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_"
                "forward_model_validation_packet_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "independent_harmonic_review": {
            "coefficient": "c_n=(1/(2*pi))*integral(tau*exp(-i*n*theta),theta=0..2*pi)",
            "a_n_relation": "a_n=2*Re(c_n)",
            "b_n_relation": "b_n=-2*Im(c_n)",
            "real_vector_order": "GAP_MAJOR_2RE_2IM_4RE_4IM_6RE_6IM",
            "real_vector_length": 150,
            "unit": "N_m",
            "complete": True,
        },
        "independent_geometry_and_torque_review": {
            "pair_distance_squared": "L_D^2+L_A^2+z^2-2*q*L_D*L_A*cos(theta)",
            "pair_distance_derivative": "q*L_D*L_A*sin(theta)/r_q",
            "energy": "2*sum_q(u(r_q))",
            "torque": "-2*sum_q(u_prime(r_q)*q*L_D*L_A*sin(theta)/r_q)",
            "energy_pi_periodic": True,
            "energy_even": True,
            "torque_odd": True,
            "equal_body_label_swap_invariant": True,
            "complete": True,
        },
        "production_and_control_review": {
            "shared_function_count": 6,
            "benchmark_count": 4,
            "mutation_count": 5,
            "symmetry_phase_control_count": 7,
            "independent_torque_cross_check_count": 2,
            "production_side_shared": True,
            "reference_density_cubature_independent": True,
            "complete": True,
        },
        "perturbation_review": {
            "count": 16,
            "composition_order_complete": True,
            "exact_amplitude_degeneracy": [
                "TORQUE_CALIBRATION",
                "SOURCE_DENSITY_SCALE",
                "DETECTOR_DENSITY_SCALE",
            ],
            "separately_data_identifiable": False,
            "complete": True,
        },
        "jacobian_contract_review": {
            "row_count": 150,
            "column_count": 17,
            "parameter_order_complete": True,
            "numeric_base_steps_complete": False,
            "rank_deficient_projector_policy_complete": False,
            "transition_domain_complete": False,
            "refinement_acceptance_tolerances_complete": False,
            "physical_identifiability_evaluated": False,
            "complete": False,
        },
        "diagnostics": list(DIAGNOSTICS),
        "unblock_requirements": [
            {"requirement_id": f"U{index}", "requirement": text, "satisfied": False}
            for index, text in enumerate(unblock_text, start=1)
        ],
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": pass_count,
            "failure_count": len(gates) - pass_count,
            "rows": gates,
        },
        "scope": scope,
        "current_posture": {
            "packet_review": "COMPLETED",
            "principal_outcome": VERDICT,
            "deterministic_execution": "NOT_AUTHORIZED",
            "work_packages": "0_OF_10_EXECUTED",
            "deterministic_vectors": 0,
            "jacobian": "NOT_COMPUTED",
            "stage_b": "DEFERRED_NOT_AUTHORIZED",
            "empirical_constraint": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "The review verifies the deterministic harmonic, kernel, torque, "
            "benchmark, mutation, symmetry, perturbation, degeneracy, and "
            "serialization surface while blocking execution on four underdefined "
            "Jacobian-identifiability interfaces. It does not evaluate physical "
            "identifiability and authorizes no repair, execution, stochastic work, "
            "forecast, empirical claim, parameter result, or theory adoption."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Review the deterministic Yukawa torsion-balance packet.")
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
            print("deterministic validation packet review already current")
        return 0
    if current != expected:
        print("deterministic validation packet review drift")
        return 1
    print("deterministic validation packet review OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

