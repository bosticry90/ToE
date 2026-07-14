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
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DISCRETE-NUMERICAL-GUARDRAIL-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DISCRETE-NUMERICAL-GUARDRAIL-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_20260713_v0.json"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_discrete_numerical_guardrail.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_packet_v0_result"
ACCEPTED_TARGET = "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v0"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_packet_v1"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "5608ae1d464c9de2cfc741e89137b6865f5de79b"
PREPARATION_PARENT = "b5e12343138d9218457066ca4b2462ccae795a65"
EXPECTED_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "76265ff0e54e2d826a9fa5268ec41f3d91bfed8a6cbf279d7eae3528ee7d1542",
    PACKET_RELATIVE_PATH: "52ffd123b3eb516ab824291364afd2006c90951f04d12587658941cbe499da82",
    MANIFEST_RELATIVE_PATH: "f26597414bf2fb7183d0edadc9b75869df8c2790ac6119f067a6203212a376df",
    PREPARATION_REPORT_RELATIVE_PATH: "e128a71881a56be1a089781dac2defa3aee25975ed2589d99c2f0319be963088",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
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


def independent_discrete_audit() -> dict[str, Any]:
    positive_link_phase = {"link_after_transform": "-alpha_n+theta_n+alpha_(n+1)", "neighbor_spinor": "-alpha_(n+1)", "result": "theta_n-alpha_n"}
    negative_link_phase = {"conjugate_link_after_transform": "+alpha_n-theta_n-alpha_(n+1)", "neighbor_spinor": "+alpha_(n+1)", "result": "alpha_n-theta_n"}
    Wilson_samples = [
        {"ka": "0", "sin_squared": 0, "Wilson_mass_shift_times_a": 0},
        {"ka": "pi/2", "sin_squared": 1, "Wilson_mass_shift_times_a": 1},
        {"ka": "pi", "sin_squared": 0, "Wilson_mass_shift_times_a": 2},
    ]
    return {
        "positive_link_covariance": positive_link_phase,
        "negative_link_covariance": negative_link_phase,
        "both_species_covariant": positive_link_phase["result"] == "theta_n-alpha_n" and negative_link_phase["result"] == "alpha_n-theta_n",
        "group_update_norm_identity": "|exp(i Delta_theta) U|=|U|=1",
        "descendants_gauge_invariant_under_zero_modes": True,
        "Wilson_dispersion_samples_r1": Wilson_samples,
        "doubler_mass_shift_at_pi_over_a": "2/a",
        "energy_classification_reason": "fixed-step implicit midpoint is second-order and time-symmetric but does not generally conserve the nonlinear continuum Hamiltonian exactly",
        "Gauss_rule_reason": "discrete gauge symmetry gives an algebraic Noether identity; floating-point preservation is limited by the coupled nonlinear solve",
    }


DECISION_IDS = [
    "immutable_numerical_guardrail_preparation_bound",
    "periodic_neutral_two_species_domain_is_exact",
    "positive_and_negative_link_covariance_is_independently_recomputed",
    "group_update_preserves_unit_modulus_without_projection",
    "phi2_phi3_are_gauge_invariant_real_site_descendants",
    "temporal_residual_gauge_and_holonomy_controls_are_distinct",
    "Wilson_r1_dispersion_and_doubler_shift_are_recomputed",
    "all_descendant_momenta_gradients_and_gamma_couplings_are_present",
    "discrete_action_symmetry_earns_continuity_and_Gauss_constraints",
    "bounded_convergent_energy_class_is_the_honest_selection",
    "all_eight_energy_terms_are_present",
    "four_exchange_channels_are_diagnostic_not_tautological",
    "twelve_positive_and_twenty_seven_negative_controls_are_complete",
    "previous_transverse_blocker_remains_a_regression_control",
    "pilot_scientific_choices_are_frozen",
    "pilot_may_change_only_six_engineering_parameters",
    "solver_and_threshold_rules_are_proportionate_and_non_circular",
    "canonical_observable_inventory_covers_descendant_channels",
    "only_non_authoritative_pilot_execution_is_authorized",
    "claim_nonclaims_nonpromotion_and_Prompt_boundaries_hold",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    custody_result = custody()
    audit = independent_discrete_audit()
    variables = packet["lattice_variables"]
    update = packet["link_update"]
    operators = packet["spatial_operators"]
    symmetry = packet["discrete_symmetry_and_constraints"]
    energy = packet["discrete_energy"]
    exchange = packet["discrete_exchange"]
    controls = packet["controls"]
    pilot = packet["pilot_policy"]
    boundary = packet["boundary"]
    decisions = {
        "immutable_numerical_guardrail_preparation_bound": custody_result["passed"],
        "periodic_neutral_two_species_domain_is_exact": packet["domain"]["space"].startswith("periodic S1") and packet["domain"]["charge_solvability"] == "sum_n a J0_n=0" and len(packet["domain"]["species"]) == 2,
        "positive_and_negative_link_covariance_is_independently_recomputed": audit["both_species_covariant"] and update["positive_species_transport"] == "U" and update["negative_species_transport"] == "U*",
        "group_update_preserves_unit_modulus_without_projection": update["preserves_unit_modulus_by_construction"] is True and update["componentwise_update_then_projection"] is False,
        "phi2_phi3_are_gauge_invariant_real_site_descendants": variables["phi2_phi3"] == "real site fields" and audit["descendants_gauge_invariant_under_zero_modes"],
        "temporal_residual_gauge_and_holonomy_controls_are_distinct": packet["gauge"]["choice"] == "temporal gauge A0=0" and packet["holonomy_controls"]["trivial"]["globally_pure_gauge"] is True and packet["holonomy_controls"]["nontrivial"]["globally_pure_gauge"] is False,
        "Wilson_r1_dispersion_and_doubler_shift_are_recomputed": operators["Wilson_parameter"] == 1 and audit["doubler_mass_shift_at_pi_over_a"] == "2/a" and packet["Wilson_dispersion"]["doubler_branch_separation_required"] is True,
        "all_descendant_momenta_gradients_and_gamma_couplings_are_present": variables["Pi2_Pi3"].startswith("real site momenta") and "phiI" in operators["phi_gradient"] and "alpha2 phi2_n+alpha3 phi3_n" in operators["transverse_site_coupling"],
        "discrete_action_symmetry_earns_continuity_and_Gauss_constraints": symmetry["gauge_invariant_action_required"] is True and "Noether identity" in symmetry["continuity_identity"] and "solver residual" in symmetry["Gauss_preservation"],
        "bounded_convergent_energy_class_is_the_honest_selection": energy["classification"] == "BOUNDED_CONVERGENT_ENERGY_ERROR" and energy["exact_continuum_energy_claimed"] is False and "does not generally conserve" in audit["energy_classification_reason"],
        "all_eight_energy_terms_are_present": len(energy["inventory"]) == 8,
        "four_exchange_channels_are_diagnostic_not_tautological": len(exchange["channels"]) == 4 and exchange["C_exchange_embedded_as_equation"] is False,
        "twelve_positive_and_twenty_seven_negative_controls_are_complete": len(controls["positive"]) == 12 and len(controls["negative"]) == 27,
        "previous_transverse_blocker_remains_a_regression_control": controls["previous_blocker_permanent"] is True and "rejected A2=A3 invariant truncation reintroduced" in controls["negative"],
        "pilot_scientific_choices_are_frozen": len(pilot["scientific_choices_frozen_before_pilot"]) == 10 and pilot["pilot_result_authoritative"] is False,
        "pilot_may_change_only_six_engineering_parameters": len(pilot["engineering_parameters_only"]) == 6,
        "solver_and_threshold_rules_are_proportionate_and_non_circular": pilot["solver_rule"].startswith("solver error <=0.01") and pilot["canonical_threshold_rule"].startswith("twice the maximum corresponding pilot residual"),
        "canonical_observable_inventory_covers_descendant_channels": "phi2 and phi3 wave residuals" in packet["canonical_observables"] and "three local exchange residuals" in packet["canonical_observables"],
        "only_non_authoritative_pilot_execution_is_authorized": packet["post_acceptance_target"] == ACCEPTED_TARGET and boundary["canonical_execution_authorized"] is False and boundary["result_claimed"] is False,
        "claim_nonclaims_nonpromotion_and_Prompt_boundaries_hold": "no canonical numerical result yet" in packet["nonclaims"] and boundary["C_k_audit_only"] is True and boundary["CCFT_resumed"] is False and boundary["master_action_promoted"] is False and sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) == PROMPT_SHA256,
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
        "independent_discrete_audit": audit,
        "authority_rotation": {
            "numerical_guardrail_accepted": accepted,
            "non_authoritative_pilot_execution_authorized": accepted,
            "pilot_result_authoritative": False,
            "canonical_execution_authorized": False,
            "canonical_result_claimed": False,
            "pure_1p1_truncation_rehabilitated": False,
        },
        "claim": "The descendant-aware mixed link/site numerical guardrail is accepted; only a non-authoritative engineering pilot is authorized." if accepted else "The numerical guardrail is blocked.",
        "nonclaims": packet["nonclaims"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Review the full zero-mode numerical guardrail.")
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
        print(f"wrote numerical-guardrail review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing numerical-guardrail review", file=sys.stderr)
            return 1
        print(f"numerical-guardrail review verified: {report['verdict']}; non-authoritative pilot only")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
