from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as numerical


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_result_review.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-AXIS-NORMALIZATION-REPAIR-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-AXIS-NORMALIZATION-REPAIR-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_PACKET_20260713_v0.json"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair.py"
PREPARATION_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessAxisNormalizationRepairPacket.lean"
NUMERICAL_IMPLEMENTATION_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_PACKET_RESULT_REVIEW_20260713_v0.json"
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_packet_v0_result"
SELECTED_NEXT_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v1"
VERDICT = "ACCEPT_AXIS_NORMALIZATION_REPAIR"
SELECTED_CANDIDATE_ID = "REST_NUMBER_POSITIVE_REFERENCE_LOADING"
HISTORICAL_AXIS_ID = "F_PERP_INITIAL_SIGNED_TOTAL_v0"
REPLACEMENT_AXIS_ID = "F_PERP_POSITIVE_LOADING_INITIAL_v1"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "ad18e99bc42f61c16e84dd8b02499711ab3d6685"
PREPARATION_PARENT = "42dc17bbf0e8aac579d09de19ff034650f204d1a"
EXPECTED_PREPARATION_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "c74491ba453cffc7634c60a402cf3d3faa8bb8048bdceeee4226ff098a032db0",
    PACKET_RELATIVE_PATH: "7863ae08a12841f3dba9e9a5a7b2375af8ec9c1b4ae8eef9918d15bbad3bfb88",
    MANIFEST_RELATIVE_PATH: "003a9a556c6f1536371b805ae793440db2e5e325bc4371ad3cad2d89f0081bb6",
    PREPARATION_REPORT_RELATIVE_PATH: "83015c24fcb2266ee52c3630dfd56fba01147c2ef23aa3b1c82b3538fa57e2ab",
    PREPARATION_LEAN_RELATIVE_PATH: "619ef13178c7aeb7b78bb449e62c8c633bbf05ba6c0bdcaa5291c8a666836419",
}
NUMERICAL_IMPLEMENTATION_SHA256 = "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

CANDIDATE_ORDER = [
    "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY",
    "ABSOLUTE_COMPONENT_BUDGET_FRACTION",
    "GAUGE_COVARIANT_SPECTRAL_REFERENCE_LOADING",
    "REST_NUMBER_POSITIVE_REFERENCE_LOADING",
    "FIXED_PROFILE_AMPLITUDE_LOADING",
]
WEIGHTS = [5, 5, 5, 4, 4, 3, 3, 2]
INDEPENDENT_SCORES = {
    "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY": [0, 1, 0, 0, 2, 2, 2, 2],
    "ABSOLUTE_COMPONENT_BUDGET_FRACTION": [2, 1, 1, 1, 2, 1, 0, 1],
    "GAUGE_COVARIANT_SPECTRAL_REFERENCE_LOADING": [2, 2, 2, 1, 2, 1, 1, 1],
    "REST_NUMBER_POSITIVE_REFERENCE_LOADING": [2, 2, 2, 2, 2, 2, 2, 2],
    "FIXED_PROFILE_AMPLITUDE_LOADING": [2, 1, 2, 2, 2, 2, 0, 2],
}


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
        raise ValueError(f"expected JSON object: {path}")
    return value


def git_output(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT)


def bind_preparation() -> dict[str, Any]:
    if git_output("rev-parse", f"{PREPARATION_COMMIT}^").decode().strip() != PREPARATION_PARENT:
        raise ValueError("preparation parent mismatch")
    if subprocess.run(["git", "merge-base", "--is-ancestor", PREPARATION_COMMIT, "HEAD"], cwd=REPO_ROOT).returncode != 0:
        raise ValueError("preparation is not an ancestor of HEAD")
    for relative_path, digest in EXPECTED_PREPARATION_HASHES.items():
        if sha256_bytes(git_output("show", f"{PREPARATION_COMMIT}:{relative_path}")) != digest:
            raise ValueError(f"committed preparation hash mismatch: {relative_path}")
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"working preparation hash mismatch: {relative_path}")
    if sha256_path(REPO_ROOT / NUMERICAL_IMPLEMENTATION_RELATIVE_PATH) != NUMERICAL_IMPLEMENTATION_SHA256:
        raise ValueError("accepted numerical implementation changed")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        raise ValueError("Prompt.txt changed")
    return {"preparation_commit": PREPARATION_COMMIT, "preparation_parent": PREPARATION_PARENT, "bound_paths": EXPECTED_PREPARATION_HASHES}


def independent_totals() -> dict[str, int]:
    return {candidate: sum(weight * score for weight, score in zip(WEIGHTS, INDEPENDENT_SCORES[candidate], strict=True)) for candidate in CANDIDATE_ORDER}


def independently_select(threshold: int) -> str | None:
    totals = independent_totals()
    eligible = []
    for candidate in CANDIDATE_ORDER:
        scores = INDEPENDENT_SCORES[candidate]
        gates = scores[0] == 2 and scores[1] >= 1 and scores[2] >= 1 and scores[4] == 2
        if gates and totals[candidate] >= threshold:
            eligible.append(candidate)
    if not eligible:
        return None
    best = max(totals[candidate] for candidate in eligible)
    return next(candidate for candidate in CANDIDATE_ORDER if candidate in eligible and totals[candidate] == best)


def _state(delta: float, alpha: float = 1.0) -> dict[str, np.ndarray]:
    state = numerical.initial_state("full_mixed", 32, numerical.CHARGE)
    z = complex(math.cos(delta), math.sin(delta))
    for species in ("psi_plus", "psi_minus"):
        state[species][:, [1, 3]] *= z
    for field in ("phi2", "P2", "phi3", "P3"):
        state[field] *= alpha
    return state


def independent_coordinate(state: dict[str, np.ndarray]) -> dict[str, float]:
    a = numerical.LENGTH / 32
    energy = numerical.energy_components(state, a, numerical.CHARGE)
    descendant = energy["phi2"] + energy["phi3"]
    number = sum(float(a * np.sum(np.abs(state[species]) ** 2)) for species in ("psi_plus", "psi_minus"))
    base = energy["electric_fluctuating"] + energy["electric_zero_mode"] + numerical.MASS * number
    return {"descendant": descendant, "base": base, "coordinate": descendant / (descendant + base), "signed_total": sum(energy.values())}


def independent_scientific_audit() -> dict[str, Any]:
    phase_rows = []
    for delta in (-math.pi, -math.pi / 2, 0.0, math.pi / 2):
        row = independent_coordinate(_state(delta))
        row["delta_theta_psi"] = delta
        phase_rows.append(row)
    canonical = independent_coordinate(_state(0.0))
    signed_counterexample = independent_coordinate(_state(math.pi / 2))
    signed_ratio = signed_counterexample["descendant"] / signed_counterexample["signed_total"]

    gauge_state = _state(0.0)
    before = independent_coordinate(gauge_state)["coordinate"]
    x = np.arange(32) * numerical.LENGTH / 32
    lam = 0.37 * np.sin(2 * math.pi * x / numerical.LENGTH)
    transformed = {key: value.copy() for key, value in gauge_state.items()}
    transformed["theta"] += lam - np.roll(lam, -1)
    transformed["psi_plus"] *= np.exp(1j * numerical.CHARGE * lam)[:, None]
    transformed["psi_minus"] *= np.exp(-1j * numerical.CHARGE * lam)[:, None]
    after = independent_coordinate(transformed)["coordinate"]

    inverse_rows = []
    for target in (0.0, 0.2, 0.5, 0.8, 0.95):
        alpha = 0.0 if target == 0 else math.sqrt((target / (1 - target)) * canonical["base"] / canonical["descendant"])
        reconstructed = independent_coordinate(_state(math.pi / 2, alpha))["coordinate"]
        inverse_rows.append({"target": target, "alpha": alpha, "reconstructed": reconstructed, "error": abs(target - reconstructed)})
    return {
        "historical_positive_pi_over_two_ratio": signed_ratio,
        "historical_counterexample_reproduced": signed_ratio > 1.0,
        "canonical_replacement_coordinate": canonical["coordinate"],
        "canonical_positive_base": canonical["base"],
        "phase_rows": phase_rows,
        "phase_stable": max(row["coordinate"] for row in phase_rows) - min(row["coordinate"] for row in phase_rows) <= 1e-15,
        "gauge_audit": {"before": before, "after": after, "error": abs(after - before), "invariant": abs(after - before) <= 1e-15},
        "inverse_rows": inverse_rows,
        "inverse_maximum_error": max(row["error"] for row in inverse_rows),
    }


def reconstruct_decisions(packet: dict[str, Any], audit: dict[str, Any]) -> dict[str, bool]:
    packet_totals = {item["candidate_id"]: item["weighted_total"] for item in packet.get("scored_candidates", [])}
    axis = packet.get("axis_contract", {})
    replacement = axis.get("replacement_axis", {})
    authority = packet.get("authority_boundary", {})
    return {
        "exact_preparation_target": packet.get("target") == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_packet_v0",
        "exact_closed_candidate_set": packet.get("candidate_order") == CANDIDATE_ORDER,
        "all_forty_scores_reconstructed": all([row["score"] for row in next(item for item in packet["scored_candidates"] if item["candidate_id"] == candidate)["criterion_scores"]] == INDEPENDENT_SCORES[candidate] for candidate in CANDIDATE_ORDER),
        "weighted_totals_reconstructed": packet_totals == independent_totals(),
        "selection_reconstructed_at_44": independently_select(44) == SELECTED_CANDIDATE_ID == packet.get("canonical_selection", {}).get("selected_candidate_id"),
        "selection_stable_40_through_48": all(independently_select(threshold) == SELECTED_CANDIDATE_ID for threshold in (40, 42, 44, 46, 48)),
        "recommendation_not_used": packet.get("user_recommendation", {}).get("used_as_score_input") is False,
        "historical_axis_versioned_and_diagnostic_only": axis.get("historical_axis", {}).get("axis_id") == HISTORICAL_AXIS_ID and axis.get("historical_axis", {}).get("status") == "REJECTED_AS_BOUNDED_AXIS_RETAINED_AS_SIGNED_DIAGNOSTIC",
        "replacement_axis_versioned": replacement.get("axis_id") == REPLACEMENT_AXIS_ID,
        "replacement_formula_exact": replacement.get("formula") == "E_perp_initial/(E_perp_initial+E_base_positive_initial)" and replacement.get("positive_base_formula") == "E_parallel_Maxwell_initial+m*sum_s,r(N_s,r_initial)",
        "semantic_nonconfusion_explicit": replacement.get("signed_conserved_energy_remains_separate") is True and replacement.get("forbidden_interpretation") == "Fraction of the conserved signed physical energy stored in descendants.",
        "historical_counterexample_reproduced": audit["historical_counterexample_reproduced"] is True,
        "canonical_mapping_reproduced": math.isclose(audit["canonical_replacement_coordinate"], packet.get("selected_candidate_audit", {}).get("canonical_mapping", {}).get("replacement_value", math.nan), rel_tol=0.0, abs_tol=1e-15),
        "phase_gauge_and_inverse_audits_pass": audit["phase_stable"] is True and audit["gauge_audit"]["invariant"] is True and audit["inverse_maximum_error"] <= 1e-15,
        "shortcuts_rejected": all(packet.get("shortcut_policy", {}).get(key) is False for key in ("clamping_allowed", "tolerance_based_domain_repair_allowed", "absolute_value_substitution_allowed", "historical_formula_silently_widened")),
        "mutations_discriminate": len(packet.get("mutation_controls", [])) == 15 and all(item.get("passed") is True and item.get("actual_diagnostics") == [item.get("expected_diagnostic")] for item in packet["mutation_controls"]),
        "numerical_authority_remains_closed": replacement.get("exact_low_anchor_high_values_frozen") is False and authority.get("robustness_pilot_authorized") is False and authority.get("robustness_execution_authorized") is False,
        "canonical_model_and_nonclaims_preserved": all(authority.get(key) is False for key in ("canonical_result_reopened", "accepted_reduction_reopened", "action_or_stress_tensor_changed", "pillar_completion_claimed", "seam_closure_claimed", "C_k_dynamics_claimed", "CCFT_validation_claimed", "master_action_promotion_claimed")),
    }


def build_review() -> dict[str, Any]:
    binding = bind_preparation()
    packet = load_json(REPO_ROOT / PACKET_RELATIVE_PATH)
    audit = independent_scientific_audit()
    decisions = reconstruct_decisions(packet, audit)
    if not all(decisions.values()):
        raise ValueError(f"independent normalization review failed: {[key for key, value in decisions.items() if not value]}")
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": True,
        "verdict": VERDICT,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_weighted_total": independent_totals()[SELECTED_CANDIDATE_ID],
        "candidate_weighted_totals": independent_totals(),
        "historical_axis_id": HISTORICAL_AXIS_ID,
        "replacement_axis_id": REPLACEMENT_AXIS_ID,
        "independent_scientific_audit": audit,
        "review_decisions": decisions,
        "preparation_binding": binding,
        "preparation_generator_imported": False,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET,
        "authority_rotation": {
            "axis_normalization_repair_accepted": True,
            "guardrail_v1_preparation_authorized": True,
            "historical_guardrail_v0_rewritten": False,
            "historical_signed_axis_rehabilitated": False,
            "exact_parameter_values_frozen": False,
            "robustness_pilot_authorized": False,
            "robustness_execution_authorized": False,
            "canonical_E_REPRO_result_remains_accepted": True,
            "accepted_reduction_reopened": False,
            "action_or_stress_tensor_changed": False,
            "pillar_completion_authorized": False,
            "seam_closure_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_validation_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "claim_ceiling": "The versioned positive rest-number reference loading coordinate is accepted for robustness guardrail-v1 preparation only. It is a diagnostic design coordinate, not a fraction of conserved signed energy; no calibration or robustness execution is authorized.",
        "prompt_sha256": PROMPT_SHA256,
    }


def write_review() -> None:
    REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REVIEW_REPORT_PATH.write_bytes(canonical_json_bytes(build_review()))


def check_review() -> bool:
    return REVIEW_REPORT_PATH.exists() and REVIEW_REPORT_PATH.read_bytes() == canonical_json_bytes(build_review())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    if args.write:
        write_review()
    if args.check and not check_review():
        return 1
    if args.stdout:
        print(canonical_json_bytes(build_review()).decode("utf-8"), end="")
    if not (args.write or args.check or args.stdout):
        parser.error("one of --write, --check, or --stdout is required")
    return 0


if __name__ == "__main__":
    sys.exit(main())
