from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_3p1_to_1p1_reduction_consistency_result_review.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-3P1-TO-1P1-REDUCTION-CONSISTENCY-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-3P1-TO-1P1-REDUCTION-CONSISTENCY-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_20260713_v0.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v0_result"
POST_BLOCK_ROUTE_TARGET = "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0"
CORRECTION_TARGET = "prepare_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v1"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "8aa48069db94082bdb639719b549466bd92862cd"
PREPARATION_PARENT = "113dee3c4026334c535b4ba994ddb170abd0c9fe"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_3p1_to_1p1_reduction_consistency.py"
EXPECTED_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "ccc236945980e4d6cf2771564fc772c2c85165c522d9338226e54c289716e4fb",
    PACKET_RELATIVE_PATH: "14f6ff3b44e661d2fece77ddb0ca8d878762ac7f8700f042a30190cc69b67eeb",
    MANIFEST_RELATIVE_PATH: "ab7654254319d0ace1bfe95ef50e3078ff13b59c980c8bcfb012195a326ee06e",
    PREPARATION_REPORT_RELATIVE_PATH: "5af33a154a0079d4965d968833f4c3ba4cf70710e33ca9f59a88a06452d53f3c",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
TOLERANCE = 1e-12

Matrix = list[list[complex]]


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


def custody() -> dict[str, Any]:
    commit = subprocess.run(["git", "rev-parse", PREPARATION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_HASHES}
    committed: dict[str, str] = {}
    for path in EXPECTED_HASHES:
        result = subprocess.run(["git", "show", f"{PREPARATION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    passed = commit == PREPARATION_COMMIT and parent == PREPARATION_PARENT and working == EXPECTED_HASHES and committed == EXPECTED_HASHES
    return {
        "commit": commit,
        "parent": parent,
        "working_hashes": working,
        "commit_hashes": committed,
        "expected_hashes": EXPECTED_HASHES,
        "passed": passed,
    }


def product(left: Matrix, right: Matrix) -> Matrix:
    return [[sum(left[i][k] * right[k][j] for k in range(len(right))) for j in range(len(right[0]))] for i in range(len(left))]


def add(left: Matrix, right: Matrix) -> Matrix:
    return [[left[i][j] + right[i][j] for j in range(len(left[0]))] for i in range(len(left))]


def multiply_scalar(value: Matrix, scalar: complex) -> Matrix:
    return [[scalar * item for item in row] for row in value]


def identity(size: int) -> Matrix:
    return [[1 + 0j if i == j else 0j for j in range(size)] for i in range(size)]


def tensor(left: Matrix, right: Matrix) -> Matrix:
    rows = len(left) * len(right)
    columns = len(left[0]) * len(right[0])
    return [[left[i // len(right)][j // len(right[0])] * right[i % len(right)][j % len(right[0])] for j in range(columns)] for i in range(rows)]


def adjoint(value: Matrix) -> Matrix:
    return [[value[j][i].conjugate() for j in range(len(value))] for i in range(len(value[0]))]


def residual_norm(left: Matrix, right: Matrix) -> float:
    return max(abs(left[i][j] - right[i][j]) for i in range(len(left)) for j in range(len(left[0])))


def independent_algebra_audit() -> dict[str, Any]:
    sigma1: Matrix = [[0, 1], [1, 0]]
    sigma2: Matrix = [[0, -1j], [1j, 0]]
    sigma3: Matrix = [[1, 0], [0, -1]]
    two_identity = identity(2)
    gammas = [
        tensor(sigma3, two_identity),
        tensor(multiply_scalar(sigma2, 1j), two_identity),
        multiply_scalar(tensor(sigma1, sigma1), 1j),
        multiply_scalar(tensor(sigma1, sigma2), 1j),
    ]
    signature = [1, -1, -1, -1]
    clifford_residuals = []
    for mu in range(4):
        for nu in range(mu, 4):
            anticommutator = add(product(gammas[mu], gammas[nu]), product(gammas[nu], gammas[mu]))
            expected = multiply_scalar(identity(4), 2 * signature[mu] if mu == nu else 0)
            clifford_residuals.append({"mu": mu, "nu": nu, "max_residual": format(residual_norm(anticommutator, expected), ".1e")})

    def mixing_norm(matrix: Matrix) -> float:
        return max(abs(matrix[i][j]) for i in range(4) for j in range(4) if i % 2 != j % 2)

    state = [[0.5], [0.5], [0.5j], [0.5j]]
    alpha2 = product(gammas[0], gammas[2])
    alpha3 = product(gammas[0], gammas[3])
    norm = product(product(adjoint(state), identity(4)), state)[0][0]
    j2 = product(product(adjoint(state), alpha2), state)[0][0]
    j3 = product(product(adjoint(state), alpha3), state)[0][0]
    return {
        "Clifford_residuals": clifford_residuals,
        "Clifford_passed": all(float(item["max_residual"]) < TOLERANCE for item in clifford_residuals),
        "longitudinal_sector_mixing_norm": format(max(mixing_norm(gammas[0]), mixing_norm(gammas[1])), ".1e"),
        "transverse_sector_mixing_min_norm": format(min(mixing_norm(gammas[2]), mixing_norm(gammas[3])), ".1e"),
        "counterexample_norm": format(norm.real, ".12g"),
        "counterexample_j2": {"real": format(j2.real, ".12g"), "imag": format(j2.imag, ".12g")},
        "counterexample_j3": {"real": format(j3.real, ".12g"), "imag": format(j3.imag, ".12g")},
        "counterexample_sources_transverse_equation": abs(j2) > TOLERANCE or abs(j3) > TOLERANCE,
    }


DECISION_IDS = [
    "immutable_reduction_preparation_bound",
    "torus_geometry_and_Ramond_zero_mode_scope_is_exact",
    "Clifford_algebra_independently_reconstructed",
    "two_sectors_per_species_and_four_spinors_are_retained",
    "longitudinal_coupling_is_sector_diagonal",
    "transverse_coupling_is_sector_offdiagonal",
    "explicit_normalized_state_independently_sources_A2_or_A3",
    "full_zero_mode_system_is_distinguished_from_the_truncation",
    "variation_reduction_residual_matches_transverse_Maxwell_source",
    "canonical_rescaling_and_energy_interpretations_are_bounded",
    "transverse_invariance_blocker_is_confirmed",
    "blocker_does_not_expand_to_a_physical_no_go",
    "no_projection_fallback_numerics_or_execution_is_authorized",
    "Prompt_and_nonpromotion_boundaries_hold",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    custody_result = custody()
    algebra = independent_algebra_audit()
    geometry = packet["geometry"]
    gamma = packet["gamma_representation"]
    multiplicity = packet["spinor_multiplicity"]
    full = packet["full_zero_mode_reduction"]
    truncation = packet["proposed_transverse_truncation"]
    commutation = packet["variation_reduction_commutation"]
    blocker = packet["blocker"]
    decisions = {
        "immutable_reduction_preparation_bound": custody_result["passed"],
        "torus_geometry_and_Ramond_zero_mode_scope_is_exact": geometry["spacetime"] == "R_t x S1_x x T2_yz" and geometry["spinor_transverse_spin_structure"].startswith("periodic/Ramond") and geometry["zero_mode_assumption"] == ["partial_y=0", "partial_z=0"],
        "Clifford_algebra_independently_reconstructed": algebra["Clifford_passed"] and len(algebra["Clifford_residuals"]) == 10,
        "two_sectors_per_species_and_four_spinors_are_retained": multiplicity["two_1p1_sectors_per_original_4component_spinor"] is True and multiplicity["total_2component_reduced_spinors"] == 4 and multiplicity["one_sector_projected_away"] is False,
        "longitudinal_coupling_is_sector_diagonal": algebra["longitudinal_sector_mixing_norm"] == "0.0e+00" and gamma["A0_A1_coupling_does_not_mix_sectors"] is True,
        "transverse_coupling_is_sector_offdiagonal": float(algebra["transverse_sector_mixing_min_norm"]) > 0 and gamma["A2_A3_coupling_mixes_sectors"] is True,
        "explicit_normalized_state_independently_sources_A2_or_A3": algebra["counterexample_norm"] == "1" and algebra["counterexample_sources_transverse_equation"],
        "full_zero_mode_system_is_distinguished_from_the_truncation": full["retained_gauge_components"] == ["A0", "A1", "A2", "A3"] and full["full_zero_mode_variation_reduction_commutes"] is True and truncation["constraint_surface_invariant_for_all_retained_sector_data"] is False,
        "variation_reduction_residual_matches_transverse_Maxwell_source": commutation["truncated_A2_equation_residual"] == "C_variation_reduction(A2)=-mu_0 J2" and commutation["truncated_A3_equation_residual"] == "C_variation_reduction(A3)=-mu_0 J3" and commutation["counterexample_residual_nonzero"] is True,
        "canonical_rescaling_and_energy_interpretations_are_bounded": full["canonical_rescaling"]["q_1p1"] == "q_3p1/sqrt(A_perp)" and packet["energy_interpretations"]["mixing_forbidden"] is True,
        "transverse_invariance_blocker_is_confirmed": packet["analytic_result"] == "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT" and blocker["code"] == "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT",
        "blocker_does_not_expand_to_a_physical_no_go": len(blocker["does_not_refute"]) == 4 and "the full 3+1 Maxwell-Dirac action" in blocker["does_not_refute"],
        "no_projection_fallback_numerics_or_execution_is_authorized": truncation["sector_polarization_adopted"] is False and packet["post_block_route_selected_automatically"] is False and blocker["numerical_guardrail_authorized"] is False and blocker["execution_authorized"] is False,
        "Prompt_and_nonpromotion_boundaries_hold": sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) == PROMPT_SHA256 and any("C_k dynamics" in item for item in packet["nonclaims"]),
    }
    ordered = [{"decision_id": item, "passed": decisions[item]} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    review_accepted = not failed
    blocker_confirmed = review_accepted
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": review_accepted,
        "verdict": "B-BLOCKED" if blocker_confirmed else "B-BLOCKED_REVIEW_FAILURE",
        "blocker_confirmed": blocker_confirmed,
        "blocker_code": "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT" if blocker_confirmed else "REVIEW_DECISION_FAILURE",
        "selected_next_target": POST_BLOCK_ROUTE_TARGET if blocker_confirmed else CORRECTION_TARGET,
        "selected_next_target_kind": "post_dirac_maxwell_reduction_blocked_route_decision_packet_v0" if blocker_confirmed else CORRECTION_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_algebra_audit": algebra,
        "post_block_route_decision_candidates": packet["post_block_route_decision_candidates"],
        "post_block_route_selected_automatically": False,
        "authority_rotation": {
            "reduction_accepted": False,
            "bounded_blocker_accepted": blocker_confirmed,
            "post_block_route_decision_preparation_authorized": blocker_confirmed,
            "numerical_guardrail_authorized": False,
            "execution_authorized": False,
            "Maxwell_Dirac_result_claimed": False,
        },
        "claim": "Independent reconstruction confirms that generic retained-sector data source A2 or A3; the requested transverse truncation is boundedly blocked and only a new route-decision preparation is authorized." if blocker_confirmed else "The reduction review failed to reproduce all required decisions.",
        "nonclaims": packet["nonclaims"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review the Maxwell-Dirac reduction consistency packet.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(expected)
        print(f"wrote reduction review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions pass")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing reduction result review", file=sys.stderr)
            return 1
        print(f"reduction result review verified: {report['verdict']}; blocker_confirmed={report['blocker_confirmed']}")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
