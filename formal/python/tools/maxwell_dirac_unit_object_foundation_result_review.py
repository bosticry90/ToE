from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import unicodedata
from fractions import Fraction
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/maxwell_dirac_unit_object_foundation_result_review.py"
PACKET_RELATIVE_PATH = "formal/output/MAXWELL-DIRAC-UNIT-OBJECT-FOUNDATION-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/MAXWELL-DIRAC-UNIT-OBJECT-FOUNDATION-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_20260713_v0.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
PREPARATION_REPORT_PATH = REPO_ROOT / PREPARATION_REPORT_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_maxwell_dirac_unit_object_foundation_packet_v0_result"
ACCEPTED_NEXT_TARGET = "prepare_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v0"
BLOCKED_NEXT_TARGET = "prepare_maxwell_dirac_unit_object_foundation_packet_v1"
REVIEW_SCHEMA_ID = "MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "4a5096d88cea14983eba966af96ee8ad28ac0e87"
PREPARATION_PARENT = "1b85995a6ba0322e9f6c0ccf95dc6987c9f80a94"
EXPECTED_HASHES = {
    "formal/python/tools/maxwell_dirac_unit_object_foundation.py": "19a8892a1feb020d36cdb46c5901116393259f6e21015db8b9e9743532ed7e50",
    PACKET_RELATIVE_PATH: "5e6aa5049194579c9c7c38f6d8784ad689ea625377d079df4c00ac9db23c54bc",
    MANIFEST_RELATIVE_PATH: "d7bc5592457e335b83609de499b9f3e3c72a57f2960cd0e9e50f2782f3bae97a",
    PREPARATION_REPORT_RELATIVE_PATH: "ea360f655417ffe6bfb590d90b4a5e4c9386b3fcc550a7057bf049607e85c4e1",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"


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
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def decode(values: list[str]) -> tuple[Fraction, ...]:
    return tuple(Fraction(value) for value in values)


def add(*values: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    return tuple(sum((value[index] for value in values), Fraction()) for index in range(5))


def scale(value: tuple[Fraction, ...], factor: int) -> tuple[Fraction, ...]:
    return tuple(Fraction(factor) * item for item in value)


def sub(left: tuple[Fraction, ...], right: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    return add(left, scale(right, -1))


def custody() -> dict[str, Any]:
    head = subprocess.run(["git", "rev-parse", PREPARATION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_HASHES}
    committed = {}
    for path in EXPECTED_HASHES:
        result = subprocess.run(["git", "show", f"{PREPARATION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    passed = head == PREPARATION_COMMIT and parent == PREPARATION_PARENT and working == EXPECTED_HASHES and committed == EXPECTED_HASHES
    return {"commit": head, "parent": parent, "working_hashes": working, "commit_hashes": committed, "expected_hashes": EXPECTED_HASHES, "passed": passed}


def independent_dimension_audit(packet: dict[str, Any]) -> dict[str, Any]:
    ledger = {item["object_id"]: decode(item["external_dimension_vector"]) for item in packet["external_dimension_ledger"]}
    expected = {
        "x_mu": (0, 1, 0, 0, 0),
        "partial_mu": (0, -1, 0, 0, 0),
        "hbar": (1, 2, -1, 0, 0),
        "c": (0, 1, -1, 0, 0),
        "mu_0": (1, 1, 0, -2, 0),
        "psi_3p1": (0, Fraction(-3, 2), 0, 0, 0),
        "A_mu_3p1": (1, 1, -1, -1, 0),
        "F_munu_3p1": (1, 0, -1, -1, 0),
        "j_number_mu_3p1": (0, -3, 0, 0, 0),
        "J_em_mu_3p1": (0, -2, -1, 1, 0),
        "L_physical_3p1": (1, -1, -2, 0, 0),
        "q_1p1_candidate": (0, -1, 0, 1, 0),
        "psi_1p1_candidate": (0, Fraction(-1, 2), 0, 0, 0),
        "A_mu_1p1_candidate": (1, 2, -1, -1, 0),
        "F_munu_1p1_candidate": (1, 1, -1, -1, 0),
        "j_number_mu_1p1_candidate": (0, -1, 0, 0, 0),
        "J_em_mu_1p1_candidate": (0, -1, -1, 1, 0),
        "L_physical_1p1_candidate": (1, 1, -2, 0, 0),
    }
    expected_vectors = {key: tuple(Fraction(item) for item in value) for key, value in expected.items()}
    vector_failures = [key for key, value in expected_vectors.items() if ledger.get(key) != value]
    d4 = packet["internal_mass_dimension_formula"]["D4"]
    d2 = packet["internal_mass_dimension_formula"]["D2"]
    internal_ok = d4["psi"] == "3/2" and d4["q"] == "0" and d4["stress_energy"] == "4" and d2["psi"] == "1/2" and d2["q"] == "1" and d2["stress_energy"] == "2"
    hbar = ledger["hbar"]
    c = ledger["c"]
    mu0 = ledger["mu_0"]
    derivative = ledger["partial_mu"]
    term_checks = {
        "D4_kinetic": add(hbar, c, scale(ledger["psi_3p1"], 2), derivative) == ledger["L_physical_3p1"],
        "D4_Maxwell": sub(scale(ledger["F_munu_3p1"], 2), mu0) == ledger["L_physical_3p1"],
        "D4_interaction": add(ledger["J_em_mu_3p1"], ledger["A_mu_3p1"]) == ledger["L_physical_3p1"],
        "D2_kinetic": add(hbar, c, scale(ledger["psi_1p1_candidate"], 2), derivative) == ledger["L_physical_1p1_candidate"],
        "D2_Maxwell": sub(scale(ledger["F_munu_1p1_candidate"], 2), mu0) == ledger["L_physical_1p1_candidate"],
        "D2_interaction": add(ledger["J_em_mu_1p1_candidate"], ledger["A_mu_1p1_candidate"]) == ledger["L_physical_1p1_candidate"],
    }
    order_ok = all(item["passed"] and decode(item["C_dim_order_residual"]) == (Fraction(),) * 5 for item in packet["C_dim_order_checks"])
    return {
        "vector_failures": vector_failures,
        "internal_dimensions_passed": internal_ok,
        "term_checks": term_checks,
        "dimension_order_passed": order_ok,
        "passed": not vector_failures and internal_ok and all(term_checks.values()) and order_ok,
    }


DECISION_IDS = [
    "immutable_foundation_preparation_bound",
    "SR_coordinate_and_restoration_conventions_are_coherent",
    "internal_mass_dimensions_independently_recomputed",
    "external_dimension_vectors_independently_recomputed",
    "D4_and_D2_action_terms_independently_balance",
    "dimension_order_commutation_independently_recomputed",
    "two_species_charge_and_cnumber_semantics_are_exact",
    "shared_action_is_real_symmetrized_and_gauge_covariant",
    "tetrad_variation_route_derives_Hilbert_not_policy_tensor",
    "current_and_exchange_signs_sum_to_total_conservation",
    "negative_frequency_diagnostic_is_not_quantum_pair_creation",
    "resolution_execution_readiness_is_accepted",
    "reduction_and_numerical_work_remain_unperformed",
    "Prompt_and_all_nonpromotion_boundaries_hold",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    custody_result = custody()
    dimensions = independent_dimension_audit(packet)
    conventions = packet["conventions"]
    action = packet["shared_action"]
    variation = packet["tetrad_variation_derivation"]
    semantics = packet["field_semantics"]
    equations = packet["derived_equations"]
    readiness = packet["resolution_execution_readiness_candidate"]
    boundary = packet["boundary"]
    decisions = {
        "immutable_foundation_preparation_bound": custody_result["passed"],
        "SR_coordinate_and_restoration_conventions_are_coherent": conventions["x0_external"] == "ct" and conventions["metric_signature"] == "+---" and conventions["electromagnetic_normalization"].startswith("rationalized SI"),
        "internal_mass_dimensions_independently_recomputed": dimensions["internal_dimensions_passed"],
        "external_dimension_vectors_independently_recomputed": not dimensions["vector_failures"],
        "D4_and_D2_action_terms_independently_balance": all(dimensions["term_checks"].values()),
        "dimension_order_commutation_independently_recomputed": dimensions["dimension_order_passed"],
        "two_species_charge_and_cnumber_semantics_are_exact": action["species"][0]["charge"] == "+q" and action["species"][1]["charge"] == "-q" and semantics["spinor_type"] == "commuting complex c-number spinor",
        "shared_action_is_real_symmetrized_and_gauge_covariant": action["real_symmetrized"] is True and "D_mu psi_+" in conventions["covariant_derivative_positive_charge"] and "D_mu psi_-" in conventions["covariant_derivative_negative_charge"],
        "tetrad_variation_route_derives_Hilbert_not_policy_tensor": variation["canonical_route"] == "HILBERT_TENSOR_FROM_ORIENTED_TETRAD_VARIATION" and variation["policy_selected_tensor_used"] is False and len(variation["ordered_steps"]) == 7,
        "current_and_exchange_signs_sum_to_total_conservation": equations["Maxwell_exchange"].endswith("J^lambda") and "+F^nu_lambda" in equations["matter_exchange"] and equations["total_conservation"].endswith("=0"),
        "negative_frequency_diagnostic_is_not_quantum_pair_creation": any("not quantum pair creation" in item for item in semantics["spectral_diagnostics"]),
        "resolution_execution_readiness_is_accepted": all(readiness[key] == 2 for key in ("evidence_authority", "object_clarity", "dependency_readiness", "restoration_clarity", "noncircularity")) and readiness["unresolved_conflicts"] == [],
        "reduction_and_numerical_work_remain_unperformed": boundary["reduction_authorized"] is False and boundary["numerical_execution_authorized"] is False,
        "Prompt_and_all_nonpromotion_boundaries_hold": prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE) and boundary["C_k_audit_only"] is True and boundary["CCFT_resumed"] is False and boundary["master_action_promoted"] is False,
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
        "selected_next_target": ACCEPTED_NEXT_TARGET if accepted else BLOCKED_NEXT_TARGET,
        "selected_next_target_kind": ACCEPTED_NEXT_TARGET if accepted else BLOCKED_NEXT_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_dimension_audit": dimensions,
        "authority_rotation": {
            "foundation_accepted": accepted,
            "resolution_execution_readiness": accepted,
            "analytic_reduction_preparation_authorized": accepted,
            "numerical_guardrail_authorized": False,
            "Maxwell_Dirac_result_claimed": False,
        },
        "nonclaims": packet["nonclaims"],
        "claim": "The unit-complete two-species c-number Maxwell-Dirac foundation is accepted; only analytic 3+1 to 1+1 reduction preparation is authorized." if accepted else "The foundation is blocked.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Review the Maxwell-Dirac unit/object foundation.")
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
        print(f"wrote Maxwell-Dirac foundation review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions pass")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing foundation review", file=sys.stderr)
            return 1
        print(f"Maxwell-Dirac foundation review verified: {report['verdict']}")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
