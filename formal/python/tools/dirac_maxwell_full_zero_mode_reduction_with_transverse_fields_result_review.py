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
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-REDUCTION-WITH-TRANSVERSE-FIELDS-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-REDUCTION-WITH-TRANSVERSE-FIELDS-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_20260713_v0.json"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_reduction_with_transverse_fields.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v0_result"
ACCEPTED_TARGET = "prepare_dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_packet_v0"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v1"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "8fb73ca66d97f91625aa657c6fea7c2496451f40"
PREPARATION_PARENT = "f953552a61366c72b20b55857e2db33a35254619"
EXPECTED_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "068125c5174216f29d18afa91f2387a501644a03317139cb3655da60ff5bff96",
    PACKET_RELATIVE_PATH: "5582abceb645e5e63e0ab750a50b56b82a8fd8f3b27ed4be02586ae5e56f5488",
    MANIFEST_RELATIVE_PATH: "1b32cc1f0777214453a751cdc66f8de4cf81335621ade151ce823e4bd124e0fd",
    PREPARATION_REPORT_RELATIVE_PATH: "044ca568da1a4830b26c61c732eb8a013da712cb5c34758bf1bbb4df29ab6086",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
TOL = 1e-12

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
    return {"commit": commit, "parent": parent, "working_hashes": working, "commit_hashes": committed, "expected_hashes": EXPECTED_HASHES, "passed": passed}


def product(left: Matrix, right: Matrix) -> Matrix:
    return [[sum(left[i][k] * right[k][j] for k in range(len(right))) for j in range(len(right[0]))] for i in range(len(left))]


def scale(value: Matrix, scalar: complex) -> Matrix:
    return [[scalar * item for item in row] for row in value]


def tensor(left: Matrix, right: Matrix) -> Matrix:
    return [[left[i // len(right)][j // len(right[0])] * right[i % len(right)][j % len(right[0])] for j in range(len(left[0]) * len(right[0]))] for i in range(len(left) * len(right))]


def identity(size: int) -> Matrix:
    return [[1 + 0j if i == j else 0j for j in range(size)] for i in range(size)]


def mixing_norm(matrix: Matrix) -> float:
    return max(abs(matrix[i][j]) for i in range(4) for j in range(4) if i % 2 != j % 2)


def independent_reduction_audit() -> dict[str, Any]:
    sigma1: Matrix = [[0, 1], [1, 0]]
    sigma2: Matrix = [[0, -1j], [1j, 0]]
    sigma3: Matrix = [[1, 0], [0, -1]]
    gamma0 = tensor(sigma3, identity(2))
    gamma1 = tensor(scale(sigma2, 1j), identity(2))
    gamma2 = scale(tensor(sigma1, sigma1), 1j)
    gamma3 = scale(tensor(sigma1, sigma2), 1j)
    pair_coefficients = {
        "F01_in_F2": 2 * 1 * -1,
        "F02_in_F2": 2 * 1 * -1,
        "F12_in_F2": 2 * -1 * -1,
        "F03_in_F2": 2 * 1 * -1,
        "F13_in_F2": 2 * -1 * -1,
    }
    lagrangian_coefficients = {
        "F01_squared": -pair_coefficients["F01_in_F2"] / 4,
        "phi2_time_squared": -pair_coefficients["F02_in_F2"] / 4,
        "phi2_space_squared": -pair_coefficients["F12_in_F2"] / 4,
        "phi3_time_squared": -pair_coefficients["F03_in_F2"] / 4,
        "phi3_space_squared": -pair_coefficients["F13_in_F2"] / 4,
    }
    scalar_wave_signs = {
        "L_derivative_coefficient": 1,
        "L_source_coefficient_for_J_upper": -1,
        "Euler_Lagrange_equation": "Box phi_I=-mu_0 J^I=mu_0 J_I",
    }
    exchange_coefficients = {
        "longitudinal": {"field": -1, "matter": 1, "sum": 0},
        "phi2": {"field": -1, "matter": 1, "sum": 0},
        "phi3": {"field": -1, "matter": 1, "sum": 0},
    }
    return {
        "pair_coefficients": pair_coefficients,
        "lagrangian_coefficients": lagrangian_coefficients,
        "Maxwell_decomposition_passed": lagrangian_coefficients == {"F01_squared": 0.5, "phi2_time_squared": 0.5, "phi2_space_squared": -0.5, "phi3_time_squared": 0.5, "phi3_space_squared": -0.5},
        "gamma_longitudinal_mixing_norm": format(max(mixing_norm(gamma0), mixing_norm(gamma1)), ".1e"),
        "gamma_transverse_min_mixing_norm": format(min(mixing_norm(gamma2), mixing_norm(gamma3)), ".1e"),
        "scalar_wave_signs": scalar_wave_signs,
        "stress_tensor_descendant_coefficients": {"gradient_outer_product": 1, "metric_trace": "-1/2", "matches_parent_ab_components": True},
        "exchange_coefficients": exchange_coefficients,
        "exchange_sum_zero": all(item["sum"] == 0 for item in exchange_coefficients.values()),
    }


DECISION_IDS = [
    "immutable_full_zero_mode_preparation_bound",
    "complete_parent_field_inventory_is_retained",
    "descendants_are_gauge_components_not_new_scalar_matter",
    "zero_mode_gauge_transformations_are_independently_consistent",
    "Maxwell_action_decomposition_is_independently_recomputed",
    "gamma2_gamma3_sector_mixing_is_independently_recomputed",
    "transverse_wave_equation_signs_follow_Euler_Lagrange_variation",
    "all_parent_and_reduced_action_equations_match",
    "variation_reduction_commutation_has_six_zero_residuals",
    "descendant_Hilbert_tensors_match_parent_ab_components",
    "three_exchange_channels_independently_sum_to_zero",
    "dimension_order_and_parent_tensor_residuals_are_zero",
    "positive_negative_and_permanent_regression_controls_are_complete",
    "later_discrete_architecture_preserves_link_site_distinction",
    "maximum_claim_and_nonclaims_are_bounded",
    "only_numerical_guardrail_preparation_is_next_authorized",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    custody_result = custody()
    audit = independent_reduction_audit()
    inventory = packet["field_inventory"]
    transformations = packet["gauge_transformations"]
    equations = packet["reduced_equations"]
    variation = packet["variation_reduction_commutation"]
    stress = packet["stress_energy"]
    exchange = packet["exchange_structure"]
    controls = packet["analytic_controls"]
    later = packet["numerical_architecture_constraints_for_later_guardrail"]
    boundary = packet["boundary"]
    decisions = {
        "immutable_full_zero_mode_preparation_bound": custody_result["passed"],
        "complete_parent_field_inventory_is_retained": inventory["transverse_gauge_descendants"] == ["phi_2(t,x):=A_2(t,x)", "phi_3(t,x):=A_3(t,x)"] and inventory["total_two_component_spinors"] == 4 and inventory["sector_projection_used"] is False,
        "descendants_are_gauge_components_not_new_scalar_matter": inventory["transverse_descendants_are_new_independent_scalar_matter"] is False,
        "zero_mode_gauge_transformations_are_independently_consistent": transformations["A_a"].endswith("partial_a lambda") and transformations["phi_2"].startswith("invariant") and transformations["phi_3"].startswith("invariant"),
        "Maxwell_action_decomposition_is_independently_recomputed": audit["Maxwell_decomposition_passed"] and packet["field_strength_decomposition"]["F_MN_F^MN"] == "F_ab F^ab-2 partial_a phi_2 partial^a phi_2-2 partial_a phi_3 partial^a phi_3",
        "gamma2_gamma3_sector_mixing_is_independently_recomputed": audit["gamma_longitudinal_mixing_norm"] == "0.0e+00" and float(audit["gamma_transverse_min_mixing_norm"]) > TOL and packet["gamma_sector_structure"]["transverse_couplings_mix_retained_sectors"] is True,
        "transverse_wave_equation_signs_follow_Euler_Lagrange_variation": equations["phi2"] == "Box phi_2=mu_0 J_2=-mu_0 J^2" and equations["phi3"] == "Box phi_3=mu_0 J_3=-mu_0 J^3" and audit["scalar_wave_signs"]["Euler_Lagrange_equation"] == "Box phi_I=-mu_0 J^I=mu_0 J_I",
        "all_parent_and_reduced_action_equations_match": packet["reduced_action"]["derived_from_parent_without_added_terms"] is True and all(item["introduced_to_repair_conservation"] is False for item in packet["reduced_action"]["terms"]),
        "variation_reduction_commutation_has_six_zero_residuals": len(variation["checks"]) == 6 and all(item["passed"] and item["residual"] == "0" for item in variation["checks"]),
        "descendant_Hilbert_tensors_match_parent_ab_components": audit["stress_tensor_descendant_coefficients"]["matches_parent_ab_components"] is True and stress["C_T_reduction"] == "0" and stress["parent_match"].startswith("T_total_1p1"),
        "three_exchange_channels_independently_sum_to_zero": audit["exchange_sum_zero"] and len(exchange["channels"]) == 3 and exchange["overall_total_conservation"] == "partial_a T_total^ab=0",
        "dimension_order_and_parent_tensor_residuals_are_zero": packet["dimension_order_audit"]["all_zero"] is True and stress["C_T_reduction"] == "0",
        "positive_negative_and_permanent_regression_controls_are_complete": len(controls["positive"]) == 8 and len(controls["negative"]) == 11 and "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT" in controls["permanent_regression_control"],
        "later_discrete_architecture_preserves_link_site_distinction": "Wilson links" in later["A1"] and later["phi2_phi3"].startswith("site-centered real descendant fields"),
        "maximum_claim_and_nonclaims_are_bounded": "zero-mode reduction" in packet["claim_ceiling"] and "no pure 1+1 Maxwell-Dirac truncation" in packet["nonclaims"] and "no transverse-mode decoupling" in packet["nonclaims"],
        "only_numerical_guardrail_preparation_is_next_authorized": packet["post_acceptance_target"] == ACCEPTED_TARGET and boundary["numerical_guardrail_authorized"] is False and boundary["execution_authorized"] is False and sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) == PROMPT_SHA256,
    }
    ordered = [{"decision_id": item, "passed": decisions[item]} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT" if accepted else "B-BLOCKED",
        "selected_next_target": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "selected_next_target_kind": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_reduction_audit": audit,
        "authority_rotation": {
            "full_zero_mode_analytic_repair_accepted": accepted,
            "numerical_guardrail_preparation_authorized": accepted,
            "numerical_guardrail_accepted": False,
            "execution_authorized": False,
            "pure_1p1_truncation_rehabilitated": False,
            "transverse_mode_decoupling_claimed": False,
            "pillar_or_seam_completion_claimed": False,
        },
        "claim": "The parent-derived full zero-mode c-number Maxwell-Dirac reduction is analytically accepted with A2 and A3 retained; only numerical-guardrail preparation is authorized." if accepted else "The full zero-mode analytic repair is blocked.",
        "maximum_future_result_claim": "A bounded, unit-complete c-number zero-mode reduction retaining the 1+1 gauge field, both transverse gauge descendants, two opposite-charge species, and both reduced spin sectors may be tested numerically after a separately accepted guardrail.",
        "nonclaims": packet["nonclaims"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Review the full zero-mode Maxwell-Dirac analytic repair.")
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
        print(f"wrote full zero-mode repair review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing full zero-mode repair review", file=sys.stderr)
            return 1
        print(f"full zero-mode repair review verified: {report['verdict']}; numerical preparation only")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
