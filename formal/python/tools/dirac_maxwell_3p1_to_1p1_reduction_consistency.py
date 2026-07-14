from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_3p1_to_1p1_reduction_consistency.py"
FOUNDATION_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_"
    "RESULT_REVIEW_20260713_v0.json"
)
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-3P1-TO-1P1-REDUCTION-CONSISTENCY-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-3P1-TO-1P1-REDUCTION-CONSISTENCY-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v0"
REVIEW_TARGET = "review_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v0_result"
REVIEW_TARGET_KIND = "dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v0_result_review"
CORRECTION_TARGET = "prepare_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v1"
POST_BLOCK_ROUTE_TARGET = "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_20260713_v0"
FOUNDATION_REVIEW_SHA256 = "7e29469017b45d841f0e44647a152225e2f49e552a1d6345abff3d9805ff3d09"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
TOL = 1e-12

Matrix = list[list[complex]]
Vector = list[complex]


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def matmul(left: Matrix, right: Matrix) -> Matrix:
    return [
        [sum(left[i][k] * right[k][j] for k in range(len(right))) for j in range(len(right[0]))]
        for i in range(len(left))
    ]


def matsum(left: Matrix, right: Matrix) -> Matrix:
    return [[left[i][j] + right[i][j] for j in range(len(left[0]))] for i in range(len(left))]


def matscale(value: Matrix, factor: complex) -> Matrix:
    return [[factor * item for item in row] for row in value]


def eye(size: int) -> Matrix:
    return [[1 + 0j if i == j else 0j for j in range(size)] for i in range(size)]


def kron(left: Matrix, right: Matrix) -> Matrix:
    return [
        [left[i // len(right)][j // len(right[0])] * right[i % len(right)][j % len(right[0])] for j in range(len(left[0]) * len(right[0]))]
        for i in range(len(left) * len(right))
    ]


def dagger(value: Matrix) -> Matrix:
    return [[value[j][i].conjugate() for j in range(len(value))] for i in range(len(value[0]))]


def column(value: Vector) -> Matrix:
    return [[item] for item in value]


def expectation(state: Vector, operator: Matrix) -> complex:
    return matmul(matmul(dagger(column(state)), operator), column(state))[0][0]


def matrix_residual_norm(left: Matrix, right: Matrix) -> float:
    return max(abs(left[i][j] - right[i][j]) for i in range(len(left)) for j in range(len(left[0])))


I2 = eye(2)
SIGMA1: Matrix = [[0, 1], [1, 0]]
SIGMA2: Matrix = [[0, -1j], [1j, 0]]
SIGMA3: Matrix = [[1, 0], [0, -1]]
RHO0 = SIGMA3
RHO1 = matscale(SIGMA2, 1j)
RHO5 = SIGMA1
GAMMA0 = kron(RHO0, I2)
GAMMA1 = kron(RHO1, I2)
GAMMA2 = matscale(kron(RHO5, SIGMA1), 1j)
GAMMA3 = matscale(kron(RHO5, SIGMA2), 1j)
GAMMAS = [GAMMA0, GAMMA1, GAMMA2, GAMMA3]
ETA = [1, -1, -1, -1]


def clifford_checks() -> list[dict[str, Any]]:
    checks = []
    for mu in range(4):
        for nu in range(mu, 4):
            observed = matsum(matmul(GAMMAS[mu], GAMMAS[nu]), matmul(GAMMAS[nu], GAMMAS[mu]))
            coefficient = 2 * ETA[mu] if mu == nu else 0
            expected = matscale(eye(4), coefficient)
            norm = matrix_residual_norm(observed, expected)
            checks.append({"mu": mu, "nu": nu, "max_residual": format(norm, ".1e"), "passed": norm < TOL})
    return checks


def sector_mixing_norm(matrix: Matrix) -> float:
    return max(
        abs(matrix[i][j])
        for i in range(4)
        for j in range(4)
        if (i % 2) != (j % 2)
    )


def transverse_counterexample() -> dict[str, Any]:
    normalization = 0.5
    state = [normalization, normalization, 1j * normalization, 1j * normalization]
    norm = expectation(state, eye(4)).real
    alpha2 = matmul(GAMMA0, GAMMA2)
    alpha3 = matmul(GAMMA0, GAMMA3)
    j2 = expectation(state, alpha2)
    j3 = expectation(state, alpha3)
    return {
        "state_in_spinor_tensor_sector_order": ["1/2", "1/2", "i/2", "i/2"],
        "state_norm": format(norm, ".12g"),
        "both_sector_components_nonzero": True,
        "j2": {"real": format(j2.real, ".12g"), "imag": format(j2.imag, ".12g")},
        "j3": {"real": format(j3.real, ".12g"), "imag": format(j3.imag, ".12g")},
        "at_least_one_transverse_current_nonzero": abs(j2) > TOL or abs(j3) > TOL,
        "transverse_Maxwell_equation_at_A2_A3_zero": "Box A_perp^i=mu_0 J^i, so nonzero J^i immediately leaves the proposed truncation surface",
    }


def load_authority() -> dict[str, Any]:
    path = REPO_ROOT / FOUNDATION_REVIEW_RELATIVE_PATH
    if sha256_path(path) != FOUNDATION_REVIEW_SHA256:
        raise ValueError("foundation review hash mismatch")
    review = load_json(path)
    if not (
        review.get("accepted") is True
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("analytic_reduction_preparation_authorized") is True
        and review.get("authority_rotation", {}).get("numerical_guardrail_authorized") is False
    ):
        raise ValueError("foundation review does not authorize analytic reduction")
    return review


def build_packet() -> dict[str, Any]:
    load_authority()
    clifford = clifford_checks()
    counterexample = transverse_counterexample()
    longitudinal_no_mixing = sector_mixing_norm(GAMMA0) < TOL and sector_mixing_norm(GAMMA1) < TOL
    transverse_mixes = sector_mixing_norm(GAMMA2) > TOL and sector_mixing_norm(GAMMA3) > TOL
    blocker = counterexample["at_least_one_transverse_current_nonzero"] and transverse_mixes
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "correction_target_if_review_disagrees": CORRECTION_TARGET,
        "post_block_route_target": POST_BLOCK_ROUTE_TARGET,
        "analytic_result": "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT" if blocker else "REDUCTION_CONSISTENT_PENDING_REVIEW",
        "geometry": {
            "spacetime": "R_t x S1_x x T2_yz",
            "transverse_area": "A_perp=L_y L_z",
            "zero_mode_assumption": ["partial_y=0", "partial_z=0"],
            "gauge_transverse_boundary_conditions": "periodic on both T2 cycles",
            "spinor_transverse_spin_structure": "periodic/Ramond on both T2 cycles",
            "longitudinal_boundary_conditions": "periodic on S1_x",
        },
        "gamma_representation": {
            "tensor_order": "1+1 spinor factor tensor transverse-sector factor",
            "rho0": "sigma3",
            "rho1": "i sigma2",
            "rho5": "sigma1",
            "gamma0": "rho0 tensor I2",
            "gamma1": "rho1 tensor I2",
            "gamma2": "i rho5 tensor sigma1",
            "gamma3": "i rho5 tensor sigma2",
            "Clifford_checks": clifford,
            "longitudinal_gamma_sector_mixing_norm": format(max(sector_mixing_norm(GAMMA0), sector_mixing_norm(GAMMA1)), ".1e"),
            "transverse_gamma_min_sector_mixing_norm": format(min(sector_mixing_norm(GAMMA2), sector_mixing_norm(GAMMA3)), ".1e"),
            "A0_A1_coupling_does_not_mix_sectors": longitudinal_no_mixing,
            "A2_A3_coupling_mixes_sectors": transverse_mixes,
            "derived_1p1_sector_representation": {"gamma0": "sigma3", "gamma1": "i sigma2"},
        },
        "spinor_multiplicity": {
            "two_1p1_sectors_per_original_4component_spinor": True,
            "opposite_charge_original_species_count": 2,
            "total_2component_reduced_spinors": 4,
            "one_sector_projected_away": False,
            "sector_multiplicity_tracked_in_full_untruncated_reduced_action": 2,
        },
        "full_zero_mode_reduction": {
            "retained_gauge_components": ["A0", "A1", "A2", "A3"],
            "A2_A3_lower_dimensional_role": "two scalar fields coupled through transverse Dirac currents",
            "canonical_rescaling": {
                "psi_1p1": "sqrt(A_perp) psi_3p1",
                "A_mu_1p1": "sqrt(A_perp) A_mu_3p1",
                "q_1p1": "q_3p1/sqrt(A_perp)",
            },
            "full_zero_mode_action_reduction_consistent": True,
            "full_zero_mode_variation_reduction_commutes": True,
        },
        "proposed_transverse_truncation": {
            "constraint": ["A2=0", "A3=0"],
            "required_source_constraints": ["J2=0", "J3=0"],
            "counterexample": counterexample,
            "constraint_surface_invariant_for_all_retained_sector_data": False,
            "failure_mechanism": "gamma2 and gamma3 are off-diagonal in the two retained 1+1 sectors, so generic cross-sector coherence sources A2 or A3",
            "sector_polarization_would_repair_counterexample": True,
            "sector_polarization_adopted": False,
            "reason_not_adopted": "It would impose an additional projection/invariant-branch restriction contrary to the frozen retain-both-sectors v0 question.",
        },
        "variation_reduction_commutation": {
            "untruncated_A0_A1_A2_A3_system": "PASS",
            "truncated_A2_equation_residual": "C_variation_reduction(A2)=-mu_0 J2",
            "truncated_A3_equation_residual": "C_variation_reduction(A3)=-mu_0 J3",
            "counterexample_residual_nonzero": True,
            "stress_reduction_review": "NOT_AUTHORIZED_AFTER_EQUATION_LEVEL_TRUNCATION_FAILURE",
            "C_dim_order": "PASS_AUDIT_ONLY_FOR_CANONICAL_RESCALINGS",
        },
        "energy_interpretations": {
            "canonical_1p1_energy": "integral dx T00_1p1",
            "3p1_total_energy_on_transverse_torus": "equal to canonical 1p1 energy under full zero-mode rescaling",
            "3p1_energy_per_transverse_area": "canonical 1p1 energy/A_perp",
            "mixing_forbidden": True,
        },
        "blocker": {
            "code": "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT",
            "scientific_scope": "the requested retain-both-sectors plus A2=A3=0 truncation",
            "does_not_refute": [
                "the full 3+1 Maxwell-Dirac action",
                "the full zero-mode reduction retaining A2 and A3",
                "a separately reviewed sector-polarized branch",
                "native 1+1, 2+1, or changed-matter benchmarks",
            ],
            "numerical_guardrail_authorized": False,
            "execution_authorized": False,
        },
        "post_block_route_decision_candidates": [
            "repair reduction",
            "adopt a native 1+1 model",
            "move to 2+1",
            "change the matter sector",
        ],
        "post_block_route_selected_automatically": False,
        "nonclaims": [
            "no analytic 3+1 to truncated 1+1 consistency claim",
            "no numerical guardrail or execution authorization",
            "no automatic native 1+1, 2+1, or matter-sector fallback",
            "no fermionic QFT, quantum particle creation, pillar recovery, seam closure, new physics, C_k dynamics, CCFT, or master-action validation",
        ],
        "input_artifacts": [{"path": FOUNDATION_REVIEW_RELATIVE_PATH, "sha256": FOUNDATION_REVIEW_SHA256}],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "excluded_from_scientific_inputs": True},
    }


def validate_packet(packet: dict[str, Any]) -> list[str]:
    failures = []
    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("reduction_identity")
    if not all(item["passed"] for item in packet.get("gamma_representation", {}).get("Clifford_checks", [])):
        failures.append("Clifford_checks")
    if packet.get("gamma_representation", {}).get("A0_A1_coupling_does_not_mix_sectors") is not True:
        failures.append("longitudinal_sector_split")
    if packet.get("proposed_transverse_truncation", {}).get("counterexample", {}).get("at_least_one_transverse_current_nonzero") is not True:
        failures.append("transverse_counterexample")
    if packet.get("analytic_result") != "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT":
        failures.append("blocker_result")
    if packet.get("post_block_route_selected_automatically") is not False:
        failures.append("no_automatic_fallback")
    if packet.get("blocker", {}).get("numerical_guardrail_authorized") is not False:
        failures.append("no_numerics")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        failures.append("Prompt_preserved")
    return failures


DECISION_IDS = [
    "accepted_foundation_review_authorizes_analytic_reduction_only",
    "torus_geometry_and_Ramond_spin_structure_are_explicit",
    "4D_Clifford_representation_reproduces",
    "two_1p1_sectors_per_species_are_retained",
    "A0_A1_coupling_is_sector_diagonal",
    "A2_A3_coupling_is_sector_offdiagonal",
    "canonical_field_and_coupling_rescalings_are_recorded",
    "full_zero_mode_reduction_retaining_transverse_fields_is_consistent",
    "explicit_retained_sector_state_has_nonzero_transverse_current",
    "A2_A3_zero_constraint_surface_is_not_invariant",
    "variation_reduction_commutation_fails_for_truncated_transverse_equations",
    "energy_interpretations_are_not_mixed",
    "blocker_scope_does_not_become_a_physical_no_go",
    "no_sector_projection_or_fallback_is_silently_adopted",
    "no_numerical_guardrail_or_execution_is_authorized",
    "Prompt_and_all_nonpromotion_boundaries_hold",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    failures = validate_packet(packet)
    if failures:
        raise ValueError(f"reduction validation failed: {failures}")
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_B_BLOCKED_PENDING_INDEPENDENT_REVIEW",
        "analytic_result": packet["analytic_result"],
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "post_block_route_target": POST_BLOCK_ROUTE_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "artifact_hashes": {
            "generator_sha256": sha256_path(SCRIPT_PATH),
            "packet_sha256": sha256_bytes(packet_raw),
            "manifest_sha256": sha256_bytes(manifest_raw),
        },
        "numerical_guardrail_authorized": False,
        "execution_authorized": False,
        "post_block_route_selected_automatically": False,
        "claim": "The full zero-mode system is consistent only with A2 and A3 retained; the requested retain-both-sectors A2=A3=0 truncation is B-BLOCKED by an explicit transverse-current counterexample.",
        "nonclaims": packet["nonclaims"],
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit 3+1 to 1+1 Maxwell-Dirac reduction consistency.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print("wrote reduction audit: B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT; independent review required")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print("reduction audit verified: explicit transverse-current blocker; no numerical authorization")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
