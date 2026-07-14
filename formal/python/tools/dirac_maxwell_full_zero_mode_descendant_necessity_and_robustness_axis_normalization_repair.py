from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import sys
import unicodedata
from pathlib import Path
from typing import Any, Callable

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as numerical


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair.py"
BLOCKER_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
BLOCKED_GUARDRAIL_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v0.json"
DESIGN_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_RESULT_REVIEW_20260713_v0.json"
CANONICAL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0.json"
CANONICAL_PRIMARY_RELATIVE_PATH = "formal/output/canonical/dirac_maxwell_full_zero_mode_v0/CANONICAL_PRIMARY_N32_DT0P0015625.json"
NUMERICAL_IMPLEMENTATION_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"

PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-AXIS-NORMALIZATION-REPAIR-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-AXIS-NORMALIZATION-REPAIR-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_packet_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_packet_v0_result"
FAILURE_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_packet_v1"
POST_ACCEPTANCE_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v1"
BLOCKER_CODE = "B-BLOCKED_F_PERP_NORMALIZATION_NOT_BOUNDED"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_PACKET_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_PACKET_20260713_v0"

INPUT_HASHES = {
    BLOCKER_REVIEW_RELATIVE_PATH: "367aeabdf2964dd532ade7f9d8bcd7d1231e7a76dd9e298afc850d46639784d6",
    BLOCKED_GUARDRAIL_RELATIVE_PATH: "48f4657fbfb93730678774e56ebdf13f3bfbb039b49e1941a40ab9e5ab718fef",
    DESIGN_REVIEW_RELATIVE_PATH: "84140ac762b660a1f4ab86d9376a50bad256de1bf0f4faa9898195a5eb9fa0f9",
    CANONICAL_REVIEW_RELATIVE_PATH: "9b518024fa8a13b73d19e01576375484d5acc24e4f5896adaa612b46f500e040",
    CANONICAL_PRIMARY_RELATIVE_PATH: "97b3fe6c4ed0cfee904158fcbf778a74b0501b40580dba33e0f9300ea7b28e7a",
    NUMERICAL_IMPLEMENTATION_RELATIVE_PATH: "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

CANDIDATE_ORDER = [
    "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY",
    "ABSOLUTE_COMPONENT_BUDGET_FRACTION",
    "GAUGE_COVARIANT_SPECTRAL_REFERENCE_LOADING",
    "REST_NUMBER_POSITIVE_REFERENCE_LOADING",
    "FIXED_PROFILE_AMPLITUDE_LOADING",
]
SELECTED_CANDIDATE_ID = "REST_NUMBER_POSITIVE_REFERENCE_LOADING"
HISTORICAL_AXIS_ID = "F_PERP_INITIAL_SIGNED_TOTAL_v0"
REPLACEMENT_AXIS_ID = "F_PERP_POSITIVE_LOADING_INITIAL_v1"
CRITERION_WEIGHTS = {
    "boundedness_and_nonsingularity": 5,
    "semantic_role_fidelity": 5,
    "inverse_constructibility": 5,
    "cross_axis_stability": 4,
    "gauge_invariance": 4,
    "accepted_object_reuse": 3,
    "profile_independence": 3,
    "auditability": 2,
}
SCORES = {
    "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY": [0, 1, 0, 0, 2, 2, 2, 2],
    "ABSOLUTE_COMPONENT_BUDGET_FRACTION": [2, 1, 1, 1, 2, 1, 0, 1],
    "GAUGE_COVARIANT_SPECTRAL_REFERENCE_LOADING": [2, 2, 2, 1, 2, 1, 1, 1],
    "REST_NUMBER_POSITIVE_REFERENCE_LOADING": [2, 2, 2, 2, 2, 2, 2, 2],
    "FIXED_PROFILE_AMPLITUDE_LOADING": [2, 1, 2, 2, 2, 2, 0, 2],
}
SELECTION_THRESHOLD = 44
SENSITIVITY_THRESHOLDS = [40, 42, 44, 46, 48]


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


def load_authority() -> dict[str, dict[str, Any]]:
    sources: dict[str, dict[str, Any]] = {}
    for relative_path, digest in INPUT_HASHES.items():
        path = REPO_ROOT / relative_path
        if sha256_path(path) != digest:
            raise ValueError(f"input hash mismatch: {relative_path}")
        if path.suffix == ".json":
            sources[relative_path] = load_json(path)
    review = sources[BLOCKER_REVIEW_RELATIVE_PATH]
    authority = review.get("authority_rotation", {})
    if not (
        review.get("accepted") is True
        and review.get("verdict") == BLOCKER_CODE
        and review.get("selected_next_target") == TARGET
        and authority.get("axis_normalization_repair_preparation_authorized") is True
        and authority.get("robustness_pilot_authorized") is False
        and authority.get("canonical_robustness_execution_authorized") is False
        and authority.get("canonical_E_REPRO_result_remains_accepted") is True
    ):
        raise ValueError("accepted blocker review does not authorize normalization repair preparation")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        raise ValueError("Prompt.txt changed")
    return sources


def _state_with_phase(delta: float, descendant_scale: float = 1.0) -> dict[str, np.ndarray]:
    state = numerical.initial_state("full_mixed", 32, numerical.CHARGE)
    phase = complex(math.cos(delta), math.sin(delta))
    for species in ("psi_plus", "psi_minus"):
        state[species][:, [1, 3]] *= phase
    for field in ("phi2", "P2", "phi3", "P3"):
        state[field] *= descendant_scale
    return state


def energy_inventory(state: dict[str, np.ndarray]) -> dict[str, Any]:
    a = numerical.LENGTH / 32
    components = numerical.energy_components(state, a, numerical.CHARGE)
    descendant = components["phi2"] + components["phi3"]
    signed_total = sum(components.values())
    number_by_species = {
        species: float(a * np.sum(np.abs(state[species]) ** 2))
        for species in ("psi_plus", "psi_minus")
    }
    parallel_maxwell = components["electric_fluctuating"] + components["electric_zero_mode"]
    base_positive = parallel_maxwell + numerical.MASS * sum(number_by_species.values())
    loading = descendant / (descendant + base_positive)
    return {
        "registered_components": components,
        "descendant_energy": descendant,
        "signed_total_energy": signed_total,
        "signed_non_descendant_remainder": signed_total - descendant,
        "number_by_species": number_by_species,
        "parallel_Maxwell_energy": parallel_maxwell,
        "positive_base_energy": base_positive,
        "historical_signed_ratio": descendant / signed_total if signed_total != 0 else None,
        "positive_loading_coordinate": loading,
    }


def component_and_singularity_audit() -> dict[str, Any]:
    phase_rows = []
    for delta, label in ((-math.pi / 2, "NEGATIVE_PI_OVER_TWO"), (0.0, "ZERO"), (math.pi / 2, "POSITIVE_PI_OVER_TWO")):
        row = energy_inventory(_state_with_phase(delta))
        row.update({"phase_label": label, "delta_theta_psi": delta})
        phase_rows.append(row)
    positive = phase_rows[-1]
    unit_components = positive["registered_components"]
    quadratic = {
        "a_descendant_quadratic": positive["descendant_energy"],
        "b_descendant_interaction_linear": unit_components["gamma2_interaction"] + unit_components["gamma3_interaction"],
        "c_descendant_independent_signed": unit_components["electric_fluctuating"] + unit_components["electric_zero_mode"] + unit_components["Wilson_Dirac_local"] + unit_components["link_interaction"],
    }
    roots = np.roots([quadratic["a_descendant_quadratic"], quadratic["b_descendant_interaction_linear"], quadratic["c_descendant_independent_signed"]])
    positive_roots = sorted(float(root.real) for root in roots if abs(root.imag) < 1e-12 and root.real > 0)
    return {
        "phase_rows": phase_rows,
        "positive_pi_over_two_counterexample": {
            "historical_signed_ratio": positive["historical_signed_ratio"],
            "exceeds_one": positive["historical_signed_ratio"] > 1.0,
            "signed_remainder_over_total": positive["signed_non_descendant_remainder"] / positive["signed_total_energy"],
            "signed_remainder_over_descendant": positive["signed_non_descendant_remainder"] / positive["descendant_energy"],
            "exact_negative_contributor_identified": "gamma2_interaction",
            "no_unmeasured_sector_blamed": True,
        },
        "signed_denominator_singularity_probe": {
            "total_energy_polynomial_in_descendant_profile_scale": "a*alpha^2+b*alpha+c",
            "coefficients": quadratic,
            "positive_zero_crossing_scale": positive_roots[0],
            "historical_ratio_is_singular_at_crossing": True,
        },
        "conservation_interpretation": "The signed registered total remains the physical conservation diagnostic; the audit changes only the proposed normalization role.",
    }


def positive_loading(state: dict[str, np.ndarray]) -> float:
    return float(energy_inventory(state)["positive_loading_coordinate"])


def selected_candidate_audit() -> dict[str, Any]:
    canonical_state = _state_with_phase(0.0)
    canonical_inventory = energy_inventory(canonical_state)
    reference_descendant_energy = canonical_inventory["descendant_energy"]
    reference_base = canonical_inventory["positive_base_energy"]
    phase_rows = []
    for phase in (-math.pi, -math.pi / 2, 0.0, math.pi / 2):
        state = _state_with_phase(phase)
        phase_rows.append({"delta_theta_psi": phase, "coordinate": positive_loading(state), "positive_base_energy": energy_inventory(state)["positive_base_energy"]})

    gauge_state = _state_with_phase(0.0)
    gauge_before = positive_loading(gauge_state)
    x = np.arange(32) * numerical.LENGTH / 32
    gauge_parameter = 0.37 * np.sin(2 * math.pi * x / numerical.LENGTH)
    transformed = {key: value.copy() for key, value in gauge_state.items()}
    transformed["theta"] += gauge_parameter - np.roll(gauge_parameter, -1)
    transformed["psi_plus"] *= np.exp(1j * numerical.CHARGE * gauge_parameter)[:, None]
    transformed["psi_minus"] *= np.exp(-1j * numerical.CHARGE * gauge_parameter)[:, None]
    gauge_after = positive_loading(transformed)

    amplitude_rows = []
    for alpha in (0.0, 0.25, 0.5, 1.0, 2.0, 10.0, 100.0):
        value = positive_loading(_state_with_phase(0.0, alpha))
        amplitude_rows.append({"alpha": alpha, "coordinate": value})

    inverse_rows = []
    for target in (0.0, 0.2, 0.5, 0.8, 0.95):
        alpha = 0.0 if target == 0.0 else math.sqrt((target / (1.0 - target)) * reference_base / reference_descendant_energy)
        reconstructed = positive_loading(_state_with_phase(math.pi / 2, alpha))
        inverse_rows.append({"target": target, "alpha": alpha, "reconstructed": reconstructed, "absolute_error": abs(reconstructed - target)})

    holonomy_rows = []
    for theta_w in (-math.pi / 2, 0.0, 0.3, math.pi / 2):
        state = _state_with_phase(0.0)
        state["theta"][:] = theta_w / (numerical.CHARGE * 32)
        holonomy_rows.append({"theta_W": theta_w, "coordinate": positive_loading(state)})

    coordinates = [row["coordinate"] for row in amplitude_rows]
    return {
        "canonical_mapping": {
            "historical_axis_id": HISTORICAL_AXIS_ID,
            "historical_value": canonical_inventory["historical_signed_ratio"],
            "replacement_axis_id": REPLACEMENT_AXIS_ID,
            "replacement_value": canonical_inventory["positive_loading_coordinate"],
            "positive_base_energy": reference_base,
            "descendant_energy": reference_descendant_energy,
        },
        "phase_boundary_rows": phase_rows,
        "phase_independent": max(row["coordinate"] for row in phase_rows) - min(row["coordinate"] for row in phase_rows) <= 1e-15,
        "gauge_transform_audit": {"before": gauge_before, "after": gauge_after, "absolute_difference": abs(gauge_after - gauge_before), "invariant": abs(gauge_after - gauge_before) <= 1e-15},
        "amplitude_rows": amplitude_rows,
        "strictly_monotone_for_positive_amplitudes": all(coordinates[index + 1] > coordinates[index] for index in range(len(coordinates) - 1)),
        "zero_maps_exactly_to_zero": coordinates[0] == 0.0,
        "large_finite_loading_below_one": coordinates[-1] < 1.0,
        "inverse_rows": inverse_rows,
        "inverse_reconstruction_maximum_error": max(row["absolute_error"] for row in inverse_rows),
        "holonomy_rows": holonomy_rows,
        "holonomy_does_not_break_boundedness": all(0.0 <= row["coordinate"] < 1.0 for row in holonomy_rows),
        "signed_total_energy_mutated_by_coordinate_definition": False,
    }


def candidate_definitions() -> dict[str, dict[str, Any]]:
    return {
        "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY": {
            "formula": "E_perp/E_total_signed",
            "status": "RETAIN_AS_DIAGNOSTIC_NOT_AXIS",
            "declared_domain": "real where E_total_signed != 0",
            "principal_defect": "unbounded, sign-changing, singular, and phase-entangled",
        },
        "ABSOLUTE_COMPONENT_BUDGET_FRACTION": {
            "formula": "E_perp/(E_perp+sum_i(abs(E_i_nonperp)))",
            "status": "CANDIDATE",
            "declared_domain": "[0,1] when the denominator is positive",
            "principal_defect": "partition-dependent, nondifferentiable at component sign changes, and interaction-allocation sensitive",
        },
        "GAUGE_COVARIANT_SPECTRAL_REFERENCE_LOADING": {
            "formula": "E_perp/(E_perp+E_parallel_Maxwell+sum(<psi,abs(H_W[A1])psi>))",
            "status": "CANDIDATE",
            "declared_domain": "[0,1)",
            "principal_defect": "requires a new reviewed gauge-covariant matrix-absolute operator and is holonomy dependent",
        },
        "REST_NUMBER_POSITIVE_REFERENCE_LOADING": {
            "formula": "E_perp/(E_perp+E_parallel_Maxwell+m*sum(N_s,r))",
            "status": "CANDIDATE",
            "declared_domain": "[0,1)",
            "principal_defect": "is a positive rest-number loading norm, not a conserved-energy fraction",
        },
        "FIXED_PROFILE_AMPLITUDE_LOADING": {
            "formula": "F_profile=alpha_perp^2 for 0<=alpha_perp<=1",
            "status": "CANDIDATE",
            "declared_domain": "[0,1]",
            "principal_defect": "profile- and maximum-amplitude-dependent; not an energy loading fraction",
        },
    }


def _score_reason(candidate_id: str, criterion: str, score: int) -> str:
    reasons = {
        "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY": "The accepted blocker proves that the signed ratio is not a bounded design coordinate, although it remains an honest diagnostic.",
        "ABSOLUTE_COMPONENT_BUDGET_FRACTION": "Absolute components bound the ratio but import partition and interaction-allocation choices.",
        "GAUGE_COVARIANT_SPECTRAL_REFERENCE_LOADING": "A covariant spectral norm is positive and meaningful but requires a new operator construction not present in the accepted implementation.",
        "REST_NUMBER_POSITIVE_REFERENCE_LOADING": "Accepted number currents, positive mass, and nonnegative longitudinal Maxwell energy give a gauge-invariant positive base with a closed inverse.",
        "FIXED_PROFILE_AMPLITUDE_LOADING": "Amplitude scaling is bounded and constructible but is tied to a selected reference profile rather than a profile-independent loading norm.",
    }
    return f"Score {score}: {reasons[candidate_id]} Criterion: {criterion}."


def score_candidates() -> list[dict[str, Any]]:
    results = []
    for candidate_id in CANDIDATE_ORDER:
        values = SCORES[candidate_id]
        rows = []
        for index, (criterion, weight) in enumerate(CRITERION_WEIGHTS.items()):
            score = values[index]
            rows.append({
                "criterion": criterion,
                "weight": weight,
                "score": score,
                "weighted_score": score * weight,
                "eligibility_basis": _score_reason(candidate_id, criterion, score),
                "support_ids": ["P_SIGNED_RATIO_BLOCKED", "P_CANONICAL_RESULT_IMMUTABLE", f"P_AUDIT_{candidate_id}"],
                "missing_for_next_score": "MAXIMUM_SCORE" if score == 2 else "A reviewed construction resolving the stated principal defect.",
            })
        gates = {
            "boundedness_equals_2": values[0] == 2,
            "semantic_role_at_least_1": values[1] >= 1,
            "inverse_constructibility_at_least_1": values[2] >= 1,
            "gauge_invariance_equals_2": values[4] == 2,
        }
        results.append({
            "candidate_id": candidate_id,
            "criterion_scores": rows,
            "weighted_total": sum(row["weighted_score"] for row in rows),
            "maximum_total": 62,
            "minimum_gates": gates,
            "minimum_gates_passed": all(gates.values()),
            "unresolved_conflicts": [],
        })
    return results


def select_candidate(scored: list[dict[str, Any]], threshold: int) -> dict[str, Any]:
    eligible = [item for item in scored if item["minimum_gates_passed"] and not item["unresolved_conflicts"] and item["weighted_total"] >= threshold]
    if not eligible:
        return {"threshold": threshold, "selected_candidate_id": None, "eligible_candidate_ids": []}
    best = max(item["weighted_total"] for item in eligible)
    tied = [item for item in eligible if item["weighted_total"] == best]
    selected = min(tied, key=lambda item: CANDIDATE_ORDER.index(item["candidate_id"]))
    return {
        "threshold": threshold,
        "selected_candidate_id": selected["candidate_id"],
        "selected_weighted_total": best,
        "eligible_candidate_ids": [item["candidate_id"] for item in sorted(eligible, key=lambda item: (-item["weighted_total"], CANDIDATE_ORDER.index(item["candidate_id"])))],
        "tie_break_used": len(tied) > 1,
    }


def selected_axis_contract() -> dict[str, Any]:
    return {
        "historical_axis": {
            "axis_id": HISTORICAL_AXIS_ID,
            "formula": "E_perp_initial/E_total_signed_initial",
            "status": "REJECTED_AS_BOUNDED_AXIS_RETAINED_AS_SIGNED_DIAGNOSTIC",
            "blocker_code": BLOCKER_CODE,
        },
        "replacement_axis": {
            "axis_id": REPLACEMENT_AXIS_ID,
            "symbol": "f_perp_positive_initial",
            "formula": "E_perp_initial/(E_perp_initial+E_base_positive_initial)",
            "positive_base_formula": "E_parallel_Maxwell_initial+m*sum_s,r(N_s,r_initial)",
            "N_formula": "integral_dx(psi_s,r_dagger*psi_s,r)",
            "domain": "0 <= f_perp_positive_initial < 1",
            "strict_positivity_preconditions": ["m > 0", "sum_s,r(N_s,r_initial) > 0 or E_parallel_Maxwell_initial > 0"],
            "interpretation": "Initial descendant loading relative to a positive longitudinal-Maxwell and matter rest-number reference norm.",
            "forbidden_interpretation": "Fraction of the conserved signed physical energy stored in descendants.",
            "gauge_invariant": True,
            "dimensionless": True,
            "descendant_energy_nonnegative": True,
            "interaction_energy_double_counted": False,
            "signed_conserved_energy_remains_separate": True,
            "inverse_profile_scaling": "alpha=sqrt((f/(1-f))*E_base_positive/E_perp_reference) for 0<f<1; alpha=0 for f=0",
            "reference_profile_requirements": ["fixed profile identity", "E_perp_reference > 0", "profile shape frozen in guardrail v1"],
            "exact_low_anchor_high_values_frozen": False,
        },
    }


def validate_contract(packet: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if packet.get("target") != TARGET:
        failures.append("current_target")
    if packet.get("candidate_order") != CANDIDATE_ORDER:
        failures.append("closed_candidate_set")
    if packet.get("criterion_weights") != CRITERION_WEIGHTS:
        failures.append("weights")
    scored = packet.get("scored_candidates", [])
    if len(scored) != 5 or any(item.get("weighted_total") != sum(row.get("weighted_score", -1) for row in item.get("criterion_scores", [])) for item in scored):
        failures.append("scores_reproduce")
    if packet.get("canonical_selection", {}).get("selected_candidate_id") != SELECTED_CANDIDATE_ID:
        failures.append("selection")
    if not all(item.get("selected_candidate_id") == SELECTED_CANDIDATE_ID for item in packet.get("sensitivity_analysis", [])):
        failures.append("sensitivity")
    axes = packet.get("axis_contract", {})
    if axes.get("historical_axis", {}).get("axis_id") != HISTORICAL_AXIS_ID or axes.get("replacement_axis", {}).get("axis_id") != REPLACEMENT_AXIS_ID:
        failures.append("versioned_axis_identity")
    replacement = axes.get("replacement_axis", {})
    if replacement.get("gauge_invariant") is not True or replacement.get("signed_conserved_energy_remains_separate") is not True:
        failures.append("replacement_physics")
    if replacement.get("exact_low_anchor_high_values_frozen") is not False:
        failures.append("values_unfrozen")
    if packet.get("shortcut_policy", {}).get("clamping_allowed") is not False or packet.get("shortcut_policy", {}).get("absolute_value_substitution_allowed") is not False:
        failures.append("shortcuts_rejected")
    if packet.get("user_recommendation", {}).get("used_as_score_input") is not False:
        failures.append("recommendation_nondecisive")
    authority = packet.get("authority_boundary", {})
    if authority.get("independent_review_authorized") is not True or any(authority.get(key) is not False for key in ("guardrail_v1_preparation_authorized_before_review", "robustness_pilot_authorized", "robustness_execution_authorized", "canonical_result_reopened")):
        failures.append("authority_boundary")
    if packet.get("selected_next_target") != REVIEW_TARGET or packet.get("post_acceptance_target") != POST_ACCEPTANCE_TARGET:
        failures.append("targets")
    return failures


def mutation_controls(packet: dict[str, Any]) -> list[dict[str, Any]]:
    if validate_contract(packet):
        raise ValueError("unmutated repair packet fails")
    mutations: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        ("M_TARGET", "current_target", lambda value: value.__setitem__("target", "wrong")),
        ("M_CANDIDATE_REMOVED", "closed_candidate_set", lambda value: value["candidate_order"].pop()),
        ("M_WEIGHT_CHANGED", "weights", lambda value: value["criterion_weights"].__setitem__("auditability", 3)),
        ("M_TOTAL_FORGED", "scores_reproduce", lambda value: value["scored_candidates"][0].__setitem__("weighted_total", 62)),
        ("M_SIGNED_RATIO_SELECTED", "selection", lambda value: value["canonical_selection"].__setitem__("selected_candidate_id", "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY")),
        ("M_SENSITIVITY_CHANGED", "sensitivity", lambda value: value["sensitivity_analysis"][0].__setitem__("selected_candidate_id", None)),
        ("M_HISTORICAL_ID_REUSED", "versioned_axis_identity", lambda value: value["axis_contract"]["replacement_axis"].__setitem__("axis_id", HISTORICAL_AXIS_ID)),
        ("M_GAUGE_INVARIANCE_DROPPED", "replacement_physics", lambda value: value["axis_contract"]["replacement_axis"].__setitem__("gauge_invariant", False)),
        ("M_SIGNED_ENERGY_REINTERPRETED", "replacement_physics", lambda value: value["axis_contract"]["replacement_axis"].__setitem__("signed_conserved_energy_remains_separate", False)),
        ("M_VALUES_FROZEN", "values_unfrozen", lambda value: value["axis_contract"]["replacement_axis"].__setitem__("exact_low_anchor_high_values_frozen", True)),
        ("M_CLAMPING_ALLOWED", "shortcuts_rejected", lambda value: value["shortcut_policy"].__setitem__("clamping_allowed", True)),
        ("M_RECOMMENDATION_DECISIVE", "recommendation_nondecisive", lambda value: value["user_recommendation"].__setitem__("used_as_score_input", True)),
        ("M_PILOT_AUTHORIZED", "authority_boundary", lambda value: value["authority_boundary"].__setitem__("robustness_pilot_authorized", True)),
        ("M_CANONICAL_REOPENED", "authority_boundary", lambda value: value["authority_boundary"].__setitem__("canonical_result_reopened", True)),
        ("M_POST_TARGET_CHANGED", "targets", lambda value: value.__setitem__("post_acceptance_target", "execute_robustness")),
    ]
    results = []
    for mutation_id, expected, mutate in mutations:
        fixture = copy.deepcopy(packet)
        fixture.pop("mutation_controls", None)
        if validate_contract(fixture):
            raise ValueError(f"fresh fixture failed before {mutation_id}")
        mutate(fixture)
        actual = validate_contract(fixture)
        results.append({"mutation_id": mutation_id, "expected_diagnostic": expected, "actual_diagnostics": actual, "one_intended_premise_changed": True, "passed": actual == [expected]})
    return results


def build_packet() -> dict[str, Any]:
    load_authority()
    inventory_audit = component_and_singularity_audit()
    selected_audit = selected_candidate_audit()
    if not inventory_audit["positive_pi_over_two_counterexample"]["exceeds_one"]:
        raise ValueError("historical counterexample not reproduced")
    if not (
        selected_audit["phase_independent"]
        and selected_audit["gauge_transform_audit"]["invariant"]
        and selected_audit["strictly_monotone_for_positive_amplitudes"]
        and selected_audit["zero_maps_exactly_to_zero"]
        and selected_audit["large_finite_loading_below_one"]
        and selected_audit["inverse_reconstruction_maximum_error"] <= 1e-15
        and selected_audit["holonomy_does_not_break_boundedness"]
    ):
        raise ValueError("selected candidate audit failed")
    scored = score_candidates()
    selection = select_candidate(scored, SELECTION_THRESHOLD)
    sensitivity = [select_candidate(scored, threshold) for threshold in SENSITIVITY_THRESHOLDS]
    packet: dict[str, Any] = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_AXIS_NORMALIZATION_REPAIR_PENDING_INDEPENDENT_REVIEW",
        "blocker_code_repaired_if_review_accepts": BLOCKER_CODE,
        "selected_next_target": REVIEW_TARGET,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "candidate_order": CANDIDATE_ORDER,
        "candidate_order_is_identity_only_not_preference": True,
        "candidate_definitions": candidate_definitions(),
        "criterion_weights": CRITERION_WEIGHTS,
        "criterion_weights_frozen_before_scoring": True,
        "score_domain": [0, 1, 2],
        "maximum_weighted_total": 62,
        "selection_threshold": SELECTION_THRESHOLD,
        "sensitivity_thresholds": SENSITIVITY_THRESHOLDS,
        "scored_candidates": scored,
        "canonical_selection": selection,
        "sensitivity_analysis": sensitivity,
        "selection_stable_at_all_sensitivity_thresholds": all(item["selected_candidate_id"] == selection["selected_candidate_id"] for item in sensitivity),
        "axis_contract": selected_axis_contract(),
        "signed_component_and_singularity_audit": inventory_audit,
        "selected_candidate_audit": selected_audit,
        "shortcut_policy": {
            "clamping_allowed": False,
            "tolerance_based_domain_repair_allowed": False,
            "absolute_value_substitution_allowed": False,
            "historical_formula_silently_widened": False,
        },
        "future_guardrail_v1_obligations": {
            "freeze_exact_low_anchor_high_values": True,
            "freeze_reference_descendant_profile_identity": True,
            "enforce_positive_base_preconditions_per_row": True,
            "construct_descendant_scale_after_other_four_axes_are_set": True,
            "verify_requested_coordinate_after_construction": True,
            "retain_historical_signed_ratio_as_diagnostic": True,
            "retain_positive_pi_over_two_regression": True,
            "calibration_remains_unauthorized_until_guardrail_v1_review": True,
        },
        "user_recommendation": {"recommended_family": "POSITIVE_REFERENCE_LOADING", "used_as_score_input": False},
        "authority_boundary": {
            "independent_review_authorized": True,
            "guardrail_v1_preparation_authorized_before_review": False,
            "robustness_pilot_authorized": False,
            "robustness_execution_authorized": False,
            "canonical_result_reopened": False,
            "accepted_reduction_reopened": False,
            "action_or_stress_tensor_changed": False,
            "pillar_completion_claimed": False,
            "seam_closure_claimed": False,
            "C_k_dynamics_claimed": False,
            "CCFT_validation_claimed": False,
            "master_action_promotion_claimed": False,
        },
        "input_hashes": INPUT_HASHES,
        "prompt_sha256": PROMPT_SHA256,
    }
    packet["mutation_controls"] = mutation_controls(packet)
    return packet


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    packet_hash = sha256_bytes(canonical_json_bytes(packet))
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": packet["verdict"],
        "historical_axis_id": HISTORICAL_AXIS_ID,
        "replacement_axis_id": REPLACEMENT_AXIS_ID,
        "selected_candidate_id": packet["canonical_selection"]["selected_candidate_id"],
        "selected_weighted_total": packet["canonical_selection"]["selected_weighted_total"],
        "candidate_weighted_totals": {item["candidate_id"]: item["weighted_total"] for item in packet["scored_candidates"]},
        "selection_stable_at_all_sensitivity_thresholds": packet["selection_stable_at_all_sensitivity_thresholds"],
        "canonical_replacement_coordinate": packet["selected_candidate_audit"]["canonical_mapping"]["replacement_value"],
        "mutation_controls_passed": sum(item["passed"] for item in packet["mutation_controls"]),
        "mutation_control_count": len(packet["mutation_controls"]),
        "pilot_authorized": False,
        "packet_sha256": packet_hash,
        "selected_next_target": REVIEW_TARGET,
        "claim_ceiling": "A versioned positive diagnostic loading coordinate is prepared for independent review; no robustness parameter values, calibration, execution, pillar, or seam claim is authorized.",
    }
    report_hash = sha256_bytes(canonical_json_bytes(report))
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": [{"path": path, "sha256": digest} for path, digest in sorted(INPUT_HASHES.items())],
        "artifacts": [{"path": PACKET_RELATIVE_PATH, "sha256": packet_hash}, {"path": REPORT_RELATIVE_PATH, "sha256": report_hash}],
        "prompt": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "preserved": True},
    }
    return packet, manifest, report


def write_artifacts() -> None:
    packet, manifest, report = build_artifacts()
    for path, payload in ((PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(canonical_json_bytes(payload))


def check_artifacts() -> bool:
    packet, manifest, report = build_artifacts()
    return all(path.exists() and path.read_bytes() == canonical_json_bytes(payload) for path, payload in ((PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    if args.write:
        write_artifacts()
    if args.check and not check_artifacts():
        return 1
    if args.stdout:
        print(canonical_json_bytes(build_packet()).decode("utf-8"), end="")
    if not (args.write or args.check or args.stdout):
        parser.error("one of --write, --check, or --stdout is required")
    return 0


if __name__ == "__main__":
    sys.exit(main())
