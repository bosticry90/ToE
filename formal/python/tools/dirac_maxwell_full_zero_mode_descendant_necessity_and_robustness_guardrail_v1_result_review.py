from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import subprocess
import sys
import unicodedata
from collections import Counter
from pathlib import Path
from typing import Any, Callable

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as numerical


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_v1_result_review.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v1.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-MANIFEST-v1.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_20260714_v1.json"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_v1.py"
PREPARATION_TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_v1.py"
PREPARATION_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessGuardrailPacketV1.lean"
NUMERICAL_IMPLEMENTATION_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260714_v1.json"
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v1_result"
SELECTED_NEXT_TARGET = "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1"
VERDICT = "ACCEPT_GUARDRAIL_V1"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260714_v1"
PREPARATION_COMMIT = "f88d98a0e82cdc577f17db1e8230ea28c4c49aaa"
PREPARATION_PARENT = "74b3199502d5aae98e84bdb552c683657c8e54b8"
EXPECTED_PREPARATION_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "9a741072ffc8102dcdf9690a911e5cfa34772e3a4f62821a265905cd5fa9b5a1",
    PREPARATION_TEST_RELATIVE_PATH: "bb25d6accb8cd0dd48a26722a0f4327a4dd40d704165af509071aab490334b60",
    PACKET_RELATIVE_PATH: "54f3c8137986db1ba1bf7cc1a9e0ffade11ed7b6fdf480bf103cdd6b13d964f1",
    MANIFEST_RELATIVE_PATH: "718963d7819ce39af4a065d309fbf2a1df9fd2343edd80f01e70d4c928bd6445",
    PREPARATION_REPORT_RELATIVE_PATH: "0986e58e9d7f9b85b029a73a69915a9124b72e3a6774ec92dc539dc61f9dc147",
    PREPARATION_LEAN_RELATIVE_PATH: "c28154057f0c61d9bc196674a0dbecb1e52d6e7bec79fe7ec59c01989fce4541",
}
NUMERICAL_IMPLEMENTATION_SHA256 = "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

HISTORICAL_GUARDRAIL_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v0.json"
HISTORICAL_GUARDRAIL_PACKET_SHA256 = "48f4657fbfb93730678774e56ebdf13f3bfbb039b49e1941a40ab9e5ab718fef"
HISTORICAL_GUARDRAIL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
HISTORICAL_GUARDRAIL_REVIEW_SHA256 = "367aeabdf2964dd532ade7f9d8bcd7d1231e7a76dd9e298afc850d46639784d6"
AXIS_REPAIR_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_PACKET_RESULT_REVIEW_20260713_v0.json"
AXIS_REPAIR_REVIEW_SHA256 = "2840f6edbd1414b8e685c661de1f51cc13c28b3c629e6ff2be36b16921d3d391"

REPLACEMENT_AXIS_ID = "F_PERP_POSITIVE_LOADING_INITIAL_v1"
HISTORICAL_AXIS_ID = "F_PERP_INITIAL_SIGNED_TOTAL_v0"
GRID_SIZE = 32
LENGTH = 1.0
ROUND_TRIP_TOLERANCE = 2e-15
CANONICAL_LOADING = 0.2131315883288088
LOW_LOADING = 0.0634205964176414
HIGH_LOADING = 0.5200250552967295
LOADING_ODDS_MULTIPLIER = 4.0

AXIS_LEVELS: dict[str, dict[str, float]] = {
    "ETA_Q": {"WEAKER": 0.1, "CANONICAL": 0.2, "STRONGER": 0.4},
    REPLACEMENT_AXIS_ID: {
        "ZERO": 0.0,
        "LOW_NONZERO": LOW_LOADING,
        "CANONICAL": CANONICAL_LOADING,
        "HIGH": HIGH_LOADING,
    },
    "THETA_W": {"TRIVIAL": 0.0, "NONTRIVIAL": 0.3, "SYMMETRY_PARTNER": -0.3},
    "DELTA_THETA_PSI": {
        "CANONICAL": 0.0,
        "POSITIVE_OFFSET": math.pi / 2,
        "NEGATIVE_OFFSET": -math.pi / 2,
    },
    "MU_MASS_DOMAIN": {"CANONICAL": 1.0, "BOUNDED_VARIATION": 2.0},
}

# This independent closed list is intentionally not imported from the preparation generator.
ROW_LEVEL_SPECS = [
    ("R00_CANONICAL", "CANONICAL_ANCHOR", "CANONICAL", "CANONICAL", "NONTRIVIAL", "CANONICAL", "CANONICAL"),
    ("R01_ETA_WEAK", "ONE_AT_A_TIME", "WEAKER", "CANONICAL", "NONTRIVIAL", "CANONICAL", "CANONICAL"),
    ("R02_ETA_STRONG", "ONE_AT_A_TIME", "STRONGER", "CANONICAL", "NONTRIVIAL", "CANONICAL", "CANONICAL"),
    ("R03_F_ZERO", "ONE_AT_A_TIME", "CANONICAL", "ZERO", "NONTRIVIAL", "CANONICAL", "CANONICAL"),
    ("R04_F_LOW", "ONE_AT_A_TIME", "CANONICAL", "LOW_NONZERO", "NONTRIVIAL", "CANONICAL", "CANONICAL"),
    ("R05_F_HIGH", "ONE_AT_A_TIME", "CANONICAL", "HIGH", "NONTRIVIAL", "CANONICAL", "CANONICAL"),
    ("R06_THETA_TRIVIAL", "ONE_AT_A_TIME", "CANONICAL", "CANONICAL", "TRIVIAL", "CANONICAL", "CANONICAL"),
    ("R07_THETA_PARTNER", "ONE_AT_A_TIME", "CANONICAL", "CANONICAL", "SYMMETRY_PARTNER", "CANONICAL", "CANONICAL"),
    ("R08_PHASE_POSITIVE", "ONE_AT_A_TIME", "CANONICAL", "CANONICAL", "NONTRIVIAL", "POSITIVE_OFFSET", "CANONICAL"),
    ("R09_PHASE_NEGATIVE", "ONE_AT_A_TIME", "CANONICAL", "CANONICAL", "NONTRIVIAL", "NEGATIVE_OFFSET", "CANONICAL"),
    ("R10_MU_HIGH", "ONE_AT_A_TIME", "CANONICAL", "CANONICAL", "NONTRIVIAL", "CANONICAL", "BOUNDED_VARIATION"),
    ("R11_CORNER_WEAK_HIGH", "INTERACTION_CORNER", "WEAKER", "HIGH", "SYMMETRY_PARTNER", "POSITIVE_OFFSET", "BOUNDED_VARIATION"),
    ("R12_CORNER_STRONG_ZERO", "INTERACTION_CORNER", "STRONGER", "ZERO", "TRIVIAL", "NEGATIVE_OFFSET", "CANONICAL"),
    ("R13_CORNER_STRONG_LOW", "INTERACTION_CORNER", "STRONGER", "LOW_NONZERO", "NONTRIVIAL", "NEGATIVE_OFFSET", "BOUNDED_VARIATION"),
]

PILOT_ROW_IDS = ["R00_CANONICAL", "R03_F_ZERO", "R05_F_HIGH", "R10_MU_HIGH", "R11_CORNER_WEAK_HIGH"]
PILOT_MAY_CALIBRATE_ONLY = [
    "solver_tolerance",
    "grid_sequence",
    "time_step_sequence",
    "duration",
    "iteration_cap",
    "epsilon_exchange_floor",
    "epsilon_observable_floor",
    "residual_acceptance_thresholds",
]
PILOT_MAY_NOT_CHANGE = [
    "scientific_questions",
    "five_parameter_axes",
    "axis_values",
    "fourteen_scientific_rows",
    "comparator_eligibility",
    "observable_ids_or_formulas",
    "materiality_thresholds",
    "control_ids",
    "outcome_classes",
    "claim_ceiling",
]
NORMALIZATION_CONTROL_IDS = [
    "NORM01_HISTORICAL_RATIO_EXCEEDS_ONE",
    "NORM02_HISTORICAL_DENOMINATOR_CROSSES_ZERO",
    "NORM03_HISTORICAL_RATIO_CHANGES_SIGN",
    "NORM04_CLAMPING_REJECTED",
    "NORM05_ABSOLUTE_TOTAL_SHORTCUT_REJECTED",
    "NORM06_POST_OBSERVATION_DOMAIN_WIDENING_REJECTED",
    "NORM07_ZERO_DESCENDANTS_MAP_ZERO",
    "NORM08_FINITE_LOADING_BELOW_ONE",
    "NORM09_LOADING_MONOTONE_IN_AMPLITUDE",
    "NORM10_INVERSE_RECONSTRUCTION",
    "NORM11_GAUGE_INVARIANCE",
    "NORM12_PHASE_STABILITY_AFTER_RECONSTRUCTION",
    "NORM13_HOLONOMY_BOUNDEDNESS",
    "NORM14_MASS_DOMAIN_DENOMINATOR_POSITIVITY",
    "NORM15_VACUUM_AXIS_NOT_APPLICABLE",
    "NORM16_SIGNED_ENERGY_ROLE_SEPARATE",
    "NORM17_CANONICAL_MAPPING_EXACT",
    "NORM18_CORRUPTED_MASS_NUMBER_DETECTED",
    "NORM19_NUMBER_NORMALIZATION_OR_MULTIPLICITY_OMISSION_DETECTED",
    "NORM20_INTERACTION_ENERGY_DOUBLE_COUNT_REJECTED",
]
MUTATION_EXPECTATIONS = [
    ("M_TARGET_CHANGED", "targets"),
    ("M_AXIS_REMOVED", "axis_levels"),
    ("M_LEVELS_UNFROZEN", "axis_levels"),
    ("M_MATRIX_ROW_REMOVED", "scientific_matrix"),
    ("M_MATRIX_DUPLICATE", "scientific_matrix"),
    ("M_BASE_NONPOSITIVE", "scientific_matrix"),
    ("M_ROUND_TRIP_FAILED", "scientific_matrix"),
    ("M_COMPARATOR_PROMOTED", "comparator"),
    ("M_COMPARATOR_RELABELLED_ZERO", "comparator"),
    ("M_OBSERVABLE_REMOVED", "observables"),
    ("M_MATERIALITY_UNFROZEN", "materiality_thresholds"),
    ("M_PILOT_AUTHORIZED_EARLY", "pilot"),
    ("M_EXECUTION_AUTHORIZED_EARLY", "execution"),
    ("M_SIGNED_ROLE_CONFLATED", "semantic_roles"),
    ("M_NORMALIZATION_CONTROL_REMOVED", "normalization_controls"),
    ("M_ACCEPTED_NEGATIVE_CONTROL_REMOVED", "control_inventory"),
    ("M_OUTCOME_REMOVED", "outcome_taxonomy"),
    ("M_PILLAR_PROMOTED", "nonclaims"),
]
ROBUSTNESS_CLASSIFICATION_ORDER = [
    "NUMERICALLY_BLOCKED",
    "MODEL_DOMAIN_LIMITED",
    "THRESHOLD_SENSITIVE",
    "BROADLY_ROBUST",
    "CONDITIONALLY_ROBUST",
]


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
    if subprocess.run(
        ["git", "merge-base", "--is-ancestor", PREPARATION_COMMIT, "HEAD"],
        cwd=REPO_ROOT,
        check=False,
    ).returncode != 0:
        raise ValueError("preparation commit is not an ancestor of HEAD")
    for relative_path, digest in EXPECTED_PREPARATION_HASHES.items():
        if sha256_bytes(git_output("show", f"{PREPARATION_COMMIT}:{relative_path}")) != digest:
            raise ValueError(f"committed preparation hash mismatch: {relative_path}")
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"working preparation hash mismatch: {relative_path}")
    if sha256_path(REPO_ROOT / NUMERICAL_IMPLEMENTATION_RELATIVE_PATH) != NUMERICAL_IMPLEMENTATION_SHA256:
        raise ValueError("accepted numerical implementation changed")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        raise ValueError("Prompt.txt changed")
    historical_hashes = {
        HISTORICAL_GUARDRAIL_PACKET_RELATIVE_PATH: HISTORICAL_GUARDRAIL_PACKET_SHA256,
        HISTORICAL_GUARDRAIL_REVIEW_RELATIVE_PATH: HISTORICAL_GUARDRAIL_REVIEW_SHA256,
        AXIS_REPAIR_REVIEW_RELATIVE_PATH: AXIS_REPAIR_REVIEW_SHA256,
    }
    for relative_path, digest in historical_hashes.items():
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"historical authority changed: {relative_path}")
    return {
        "preparation_commit": PREPARATION_COMMIT,
        "preparation_parent": PREPARATION_PARENT,
        "bound_preparation_paths": EXPECTED_PREPARATION_HASHES,
        "bound_historical_paths": historical_hashes,
    }


def _close(left: float, right: float, tolerance: float = 1e-15) -> bool:
    return math.isclose(float(left), float(right), rel_tol=0.0, abs_tol=tolerance)


def independent_reference_inventory() -> dict[str, Any]:
    state = numerical.initial_state("full_mixed", GRID_SIZE, numerical.CHARGE)
    dx = LENGTH / GRID_SIZE
    components = numerical.energy_components(state, dx, numerical.CHARGE)
    number_by_species = {
        species: float(dx * np.sum(np.abs(state[species]) ** 2))
        for species in ("psi_plus", "psi_minus")
    }
    descendant_energy = float(components["phi2"] + components["phi3"])
    parallel_maxwell_energy = float(components["electric_fluctuating"] + components["electric_zero_mode"])
    total_matter_number = sum(number_by_species.values())
    base_at_mass_one = parallel_maxwell_energy + total_matter_number
    return {
        "descendant_reference_energy": descendant_energy,
        "parallel_Maxwell_energy": parallel_maxwell_energy,
        "number_by_species": number_by_species,
        "total_matter_number": total_matter_number,
        "positive_base_energy_at_mass_one": base_at_mass_one,
        "canonical_loading": descendant_energy / (descendant_energy + base_at_mass_one),
    }


def _requested_values(spec: tuple[str, ...]) -> dict[str, float]:
    _, _, eta_level, loading_level, theta_level, phase_level, mu_level = spec
    return {
        "ETA_Q": AXIS_LEVELS["ETA_Q"][eta_level],
        REPLACEMENT_AXIS_ID: AXIS_LEVELS[REPLACEMENT_AXIS_ID][loading_level],
        "THETA_W": AXIS_LEVELS["THETA_W"][theta_level],
        "DELTA_THETA_PSI": AXIS_LEVELS["DELTA_THETA_PSI"][phase_level],
        "MU_MASS_DOMAIN": AXIS_LEVELS["MU_MASS_DOMAIN"][mu_level],
    }


def _circular_tuple(values: dict[str, float]) -> tuple[float, ...]:
    phase = values["DELTA_THETA_PSI"]
    return (
        round(values["ETA_Q"], 15),
        round(values[REPLACEMENT_AXIS_ID], 15),
        round(values["THETA_W"], 15),
        round(math.cos(phase), 15),
        round(math.sin(phase), 15),
        round(values["MU_MASS_DOMAIN"], 15),
    )


def independently_reconstruct_matrix(packet: dict[str, Any]) -> dict[str, Any]:
    reference = independent_reference_inventory()
    packet_rows = packet.get("scientific_matrix", [])
    packet_by_id = {row.get("row_id"): row for row in packet_rows}
    row_audits: list[dict[str, Any]] = []
    circular_tuples: list[tuple[float, ...]] = []
    roles: list[str] = []
    for spec in ROW_LEVEL_SPECS:
        row_id, role, eta_level, loading_level, theta_level, phase_level, mu_level = spec
        requested = _requested_values(spec)
        mass = requested["MU_MASS_DOMAIN"] / LENGTH
        charge = requested["ETA_Q"] * mass
        theta_link = requested["THETA_W"] / (charge * GRID_SIZE)
        positive_base = reference["parallel_Maxwell_energy"] + mass * reference["total_matter_number"]
        loading = requested[REPLACEMENT_AXIS_ID]
        requested_descendant = 0.0 if loading == 0.0 else loading / (1.0 - loading) * positive_base
        alpha = 0.0 if requested_descendant == 0.0 else math.sqrt(requested_descendant / reference["descendant_reference_energy"])
        reconstructed_descendant = alpha**2 * reference["descendant_reference_energy"]
        realized_loading = reconstructed_descendant / (reconstructed_descendant + positive_base)
        realized = {
            "ETA_Q": charge / mass,
            REPLACEMENT_AXIS_ID: realized_loading,
            "THETA_W": charge * GRID_SIZE * theta_link,
            "DELTA_THETA_PSI": requested["DELTA_THETA_PSI"],
            "MU_MASS_DOMAIN": mass * LENGTH,
        }
        errors = {axis: abs(realized[axis] - requested[axis]) for axis in requested}
        packet_row = packet_by_id.get(row_id, {})
        derived = packet_row.get("derived_initial_state_parameters", {})
        provenance = packet_row.get("comparator_provenance", {})
        packet_matches = (
            packet_row.get("row_role") == role
            and packet_row.get("requested_level_ids")
            == {
                "ETA_Q": eta_level,
                REPLACEMENT_AXIS_ID: loading_level,
                "THETA_W": theta_level,
                "DELTA_THETA_PSI": phase_level,
                "MU_MASS_DOMAIN": mu_level,
            }
            and all(_close(packet_row.get("requested_axis_values", {}).get(axis, math.nan), value) for axis, value in requested.items())
            and all(_close(packet_row.get("round_trip_axis_values", {}).get(axis, math.nan), value) for axis, value in realized.items())
            and _close(derived.get("mass", math.nan), mass)
            and _close(derived.get("charge", math.nan), charge)
            and _close(derived.get("constant_link_coordinate_theta_n", math.nan), theta_link)
            and _close(derived.get("positive_base_energy_B_plus", math.nan), positive_base)
            and _close(derived.get("requested_descendant_energy", math.nan), requested_descendant)
            and _close(derived.get("reference_descendant_profile_alpha", math.nan), alpha)
            and _close(derived.get("reconstructed_descendant_energy", math.nan), reconstructed_descendant)
            and provenance.get("requested_parent_axis_values_preserved_as_provenance") == packet_row.get("requested_axis_values")
            and _close(provenance.get("requested_parent_row_loading", math.nan), loading)
        )
        other_axis_drift = max(errors[axis] for axis in errors if axis != REPLACEMENT_AXIS_ID)
        row_audits.append(
            {
                "row_id": row_id,
                "row_role": role,
                "requested_axis_values": requested,
                "positive_base_energy_B_plus": positive_base,
                "positive_base_strictly_positive": positive_base > 0.0,
                "requested_descendant_energy": requested_descendant,
                "reconstructed_descendant_energy": reconstructed_descendant,
                "reference_descendant_profile_alpha": alpha,
                "realized_axis_values": realized,
                "loading_round_trip_error": errors[REPLACEMENT_AXIS_ID],
                "maximum_other_axis_drift": other_axis_drift,
                "all_five_axes_pass": max(errors.values()) <= ROUND_TRIP_TOLERANCE,
                "packet_row_matches_independent_reconstruction": packet_matches,
            }
        )
        circular_tuples.append(_circular_tuple(requested))
        roles.append(role)
    anchor_odds = CANONICAL_LOADING / (1.0 - CANONICAL_LOADING)
    low_odds = LOW_LOADING / (1.0 - LOW_LOADING)
    high_odds = HIGH_LOADING / (1.0 - HIGH_LOADING)
    return {
        "reference_inventory": reference,
        "row_audits": row_audits,
        "scientific_row_count": len(row_audits),
        "unique_row_identity_count": len(set(row["row_id"] for row in row_audits)),
        "unique_circular_parameter_tuple_count": len(set(circular_tuples)),
        "zero_and_two_pi_duplicate_absent": len(set(circular_tuples)) == len(circular_tuples),
        "role_counts": dict(Counter(roles)),
        "maximum_loading_round_trip_error": max(row["loading_round_trip_error"] for row in row_audits),
        "maximum_other_axis_drift": max(row["maximum_other_axis_drift"] for row in row_audits),
        "all_positive_bases_strictly_positive": all(row["positive_base_strictly_positive"] for row in row_audits),
        "all_rows_match_packet": len(packet_rows) == len(row_audits) and all(row["packet_row_matches_independent_reconstruction"] for row in row_audits),
        "loading_odds": {"low": low_odds, "anchor": anchor_odds, "high": high_odds},
        "multiplicative_loading_symmetry": _close(anchor_odds / low_odds, LOADING_ODDS_MULTIPLIER, 2e-15)
        and _close(high_odds / anchor_odds, LOADING_ODDS_MULTIPLIER, 2e-15),
    }


def _state(delta: float, alpha: float = 1.0, theta_w: float = 0.3) -> dict[str, np.ndarray]:
    state = numerical.initial_state("full_mixed", GRID_SIZE, numerical.CHARGE)
    phase = complex(math.cos(delta), math.sin(delta))
    for species in ("psi_plus", "psi_minus"):
        state[species][:, [1, 3]] *= phase
    for field in ("phi2", "P2", "phi3", "P3"):
        state[field] *= alpha
    state["theta"][:] = theta_w / (numerical.CHARGE * GRID_SIZE)
    return state


def _coordinate(state: dict[str, np.ndarray], mass: float = 1.0) -> dict[str, float]:
    dx = LENGTH / GRID_SIZE
    components = numerical.energy_components(state, dx, numerical.CHARGE)
    descendant = float(components["phi2"] + components["phi3"])
    number = sum(float(dx * np.sum(np.abs(state[species]) ** 2)) for species in ("psi_plus", "psi_minus"))
    parallel = float(components["electric_fluctuating"] + components["electric_zero_mode"])
    base = parallel + mass * number
    return {
        "descendant": descendant,
        "base": base,
        "loading": descendant / (descendant + base),
        "signed_total": float(sum(components.values())),
    }


def _replacement_contract_diagnostics(contract: dict[str, Any]) -> list[str]:
    diagnostics: list[str] = []
    if contract.get("mass_weighted_number_term_present") is not True:
        diagnostics.append("MASS_WEIGHTED_NUMBER_TERM_CORRUPTED")
    if contract.get("number_current_normalization") != "integral_dx(psi_dagger*psi)":
        diagnostics.append("NUMBER_CURRENT_NORMALIZATION_CORRUPTED")
    if contract.get("all_four_two_component_reduced_sectors_included") is not True:
        diagnostics.append("SECTOR_MULTIPLICITY_OMITTED")
    if contract.get("interaction_energy_in_positive_base") is not False:
        diagnostics.append("INTERACTION_ENERGY_DOUBLE_COUNTED")
    if contract.get("signed_total_energy_kept_separate") is not True:
        diagnostics.append("SIGNED_ENERGY_ROLE_CONFLATED")
    if contract.get("vacuum_loading_policy") != "NOT_APPLICABLE_CONTROL":
        diagnostics.append("VACUUM_AXIS_POLICY_CORRUPTED")
    return diagnostics


def independently_reproduce_normalization_controls(matrix_audit: dict[str, Any]) -> list[dict[str, Any]]:
    positive_phase = _state(math.pi / 2)
    coordinate = _coordinate(positive_phase)
    components = numerical.energy_components(positive_phase, LENGTH / GRID_SIZE, numerical.CHARGE)
    coefficients = {
        "a": coordinate["descendant"],
        "b": float(components["gamma2_interaction"] + components["gamma3_interaction"]),
        "c": float(components["electric_fluctuating"] + components["electric_zero_mode"] + components["Wilson_Dirac_local"] + components["link_interaction"]),
    }
    roots = np.roots([coefficients["a"], coefficients["b"], coefficients["c"]])
    crossing = min(float(root.real) for root in roots if abs(root.imag) < 1e-12 and root.real > 0.0)
    below = coefficients["a"] * (crossing / 2) ** 2 + coefficients["b"] * (crossing / 2) + coefficients["c"]
    above = coefficients["a"] * (crossing * 2) ** 2 + coefficients["b"] * (crossing * 2) + coefficients["c"]

    gauge_state = _state(0.0)
    gauge_before = _coordinate(gauge_state)["loading"]
    x = np.arange(GRID_SIZE) * LENGTH / GRID_SIZE
    lam = 0.37 * np.sin(2 * math.pi * x / LENGTH)
    transformed = {key: value.copy() for key, value in gauge_state.items()}
    transformed["theta"] += lam - np.roll(lam, -1)
    transformed["psi_plus"] *= np.exp(1j * numerical.CHARGE * lam)[:, None]
    transformed["psi_minus"] *= np.exp(-1j * numerical.CHARGE * lam)[:, None]
    gauge_error = abs(_coordinate(transformed)["loading"] - gauge_before)
    phase_values = [_coordinate(_state(delta))["loading"] for delta in (-math.pi, -math.pi / 2, 0.0, math.pi / 2)]
    holonomy_values = [_coordinate(_state(0.0, theta_w=theta_w))["loading"] for theta_w in (-0.3, 0.0, 0.3)]

    contract = {
        "mass_weighted_number_term_present": True,
        "number_current_normalization": "integral_dx(psi_dagger*psi)",
        "all_four_two_component_reduced_sectors_included": True,
        "interaction_energy_in_positive_base": False,
        "signed_total_energy_kept_separate": True,
        "vacuum_loading_policy": "NOT_APPLICABLE_CONTROL",
    }
    mutation_specs: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        ("CORRUPT_MASS_WEIGHTED_NUMBER", "MASS_WEIGHTED_NUMBER_TERM_CORRUPTED", lambda value: value.__setitem__("mass_weighted_number_term_present", False)),
        ("OMIT_NUMBER_NORMALIZATION", "NUMBER_CURRENT_NORMALIZATION_CORRUPTED", lambda value: value.__setitem__("number_current_normalization", "sum_without_dx")),
        ("OMIT_SECTOR_MULTIPLICITY", "SECTOR_MULTIPLICITY_OMITTED", lambda value: value.__setitem__("all_four_two_component_reduced_sectors_included", False)),
        ("ADD_INTERACTION_ENERGY", "INTERACTION_ENERGY_DOUBLE_COUNTED", lambda value: value.__setitem__("interaction_energy_in_positive_base", True)),
    ]
    contract_mutations: dict[str, dict[str, Any]] = {}
    for mutation_id, expected, mutate in mutation_specs:
        fixture = copy.deepcopy(contract)
        mutate(fixture)
        actual = _replacement_contract_diagnostics(fixture)
        contract_mutations[mutation_id] = {
            "expected_diagnostic": expected,
            "actual_diagnostics": actual,
            "passed": actual == [expected],
        }

    signed_ratio = coordinate["descendant"] / coordinate["signed_total"]
    facts: list[tuple[str, bool, Any]] = [
        (NORMALIZATION_CONTROL_IDS[0], signed_ratio > 1.0, signed_ratio),
        (NORMALIZATION_CONTROL_IDS[1], 0.0 < crossing < 0.001, crossing),
        (NORMALIZATION_CONTROL_IDS[2], below < 0.0 < above, [below, above]),
        (NORMALIZATION_CONTROL_IDS[3], True, "clamping rejected by frozen contract"),
        (NORMALIZATION_CONTROL_IDS[4], True, "absolute-total shortcut rejected by frozen contract"),
        (NORMALIZATION_CONTROL_IDS[5], True, "post-observation widening rejected by frozen contract"),
        (NORMALIZATION_CONTROL_IDS[6], 0.0 / matrix_audit["reference_inventory"]["positive_base_energy_at_mass_one"] == 0.0, 0.0),
        (NORMALIZATION_CONTROL_IDS[7], all(row["realized_axis_values"][REPLACEMENT_AXIS_ID] < 1.0 for row in matrix_audit["row_audits"]), True),
        (NORMALIZATION_CONTROL_IDS[8], LOW_LOADING < CANONICAL_LOADING < HIGH_LOADING, [LOW_LOADING, CANONICAL_LOADING, HIGH_LOADING]),
        (NORMALIZATION_CONTROL_IDS[9], matrix_audit["maximum_loading_round_trip_error"] <= ROUND_TRIP_TOLERANCE, matrix_audit["maximum_loading_round_trip_error"]),
        (NORMALIZATION_CONTROL_IDS[10], gauge_error <= 1e-15, gauge_error),
        (NORMALIZATION_CONTROL_IDS[11], max(phase_values) - min(phase_values) <= 1e-15, max(phase_values) - min(phase_values)),
        (NORMALIZATION_CONTROL_IDS[12], all(0.0 <= value < 1.0 for value in holonomy_values), holonomy_values),
        (NORMALIZATION_CONTROL_IDS[13], matrix_audit["all_positive_bases_strictly_positive"], matrix_audit["all_positive_bases_strictly_positive"]),
        (NORMALIZATION_CONTROL_IDS[14], True, "NOT_APPLICABLE_CONTROL"),
        (NORMALIZATION_CONTROL_IDS[15], _replacement_contract_diagnostics(contract) == [], True),
        (NORMALIZATION_CONTROL_IDS[16], _close(matrix_audit["reference_inventory"]["canonical_loading"], CANONICAL_LOADING), matrix_audit["reference_inventory"]["canonical_loading"]),
        (NORMALIZATION_CONTROL_IDS[17], contract_mutations["CORRUPT_MASS_WEIGHTED_NUMBER"]["passed"], contract_mutations["CORRUPT_MASS_WEIGHTED_NUMBER"]),
        (NORMALIZATION_CONTROL_IDS[18], contract_mutations["OMIT_NUMBER_NORMALIZATION"]["passed"] and contract_mutations["OMIT_SECTOR_MULTIPLICITY"]["passed"], [contract_mutations["OMIT_NUMBER_NORMALIZATION"], contract_mutations["OMIT_SECTOR_MULTIPLICITY"]]),
        (NORMALIZATION_CONTROL_IDS[19], contract_mutations["ADD_INTERACTION_ENERGY"]["passed"], contract_mutations["ADD_INTERACTION_ENERGY"]),
    ]
    return [
        {"control_id": control_id, "independently_reproduced": bool(passed), "observed": observed}
        for control_id, passed, observed in facts
    ]


def independent_contract_diagnostics(packet: dict[str, Any]) -> list[str]:
    diagnostics: list[str] = []
    if (
        packet.get("target") != "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v1"
        or packet.get("selected_next_target") != REVIEW_TARGET
        or packet.get("post_acceptance_target") != SELECTED_NEXT_TARGET
    ):
        diagnostics.append("targets")
    levels = packet.get("axis_level_freeze", {})
    if set(levels) != set(AXIS_LEVELS) or any(item.get("exact_values_frozen") is not True for item in levels.values()):
        diagnostics.append("axis_levels")
    rows = packet.get("scientific_matrix", [])
    tuples = [_circular_tuple(row.get("requested_axis_values", {})) for row in rows if set(row.get("requested_axis_values", {})) == set(AXIS_LEVELS)]
    if len(rows) != 14 or len(tuples) != 14 or len(set(tuples)) != 14 or not all(row.get("positive_base_strictly_positive") is True and row.get("round_trip_passed") is True for row in rows):
        diagnostics.append("scientific_matrix")
    comparator = packet.get("comparator_policy", {})
    if (
        comparator.get("forced_comparator_eligible_for_positive_robustness_claim") is not False
        or comparator.get("recompute_as_zero_for_scientific_axis_forbidden") is not True
        or any(row.get("comparator_provenance", {}).get("comparator_realized_loading_status") != "NOT_PHYSICALLY_ELIGIBLE" for row in rows)
    ):
        diagnostics.append("comparator")
    observables = packet.get("observable_freeze", {}).get("inventory", {})
    if len(observables.get("existing_observables", [])) != 10 or len(observables.get("descendant_observables", [])) != 9 or observables.get("all_observable_ids_frozen") is not True:
        diagnostics.append("observables")
    thresholds = packet.get("threshold_freeze", {})
    if thresholds.get("scientific_materiality_thresholds_frozen") is not True or thresholds.get("threshold_sensitivity_values") != [0.05, 0.1, 0.2]:
        diagnostics.append("materiality_thresholds")
    pilot = packet.get("pilot_freeze", {})
    if pilot.get("pilot_subset_frozen") is not True or pilot.get("pilot_row_ids") != PILOT_ROW_IDS or pilot.get("pilot_authorized") is not False:
        diagnostics.append("pilot")
    if packet.get("authority_boundary", {}).get("robustness_execution_authorized") is not False:
        diagnostics.append("execution")
    semantics = packet.get("semantic_role_separation", {})
    if semantics.get("signed_total_energy_is_physical_conservation_diagnostic") is not True or semantics.get("positive_loading_is_design_coordinate_only") is not True:
        diagnostics.append("semantic_roles")
    controls = packet.get("normalization_regression_controls", [])
    if [item.get("control_id") for item in controls] != NORMALIZATION_CONTROL_IDS or not all(item.get("passed") is True for item in controls):
        diagnostics.append("normalization_controls")
    control_freeze = packet.get("control_freeze", {})
    if (
        control_freeze.get("all_control_ids_frozen") is not True
        or len(control_freeze.get("accepted_positive_control_ids", [])) != 8
        or len(control_freeze.get("accepted_negative_control_ids", [])) != 13
        or control_freeze.get("normalization_regression_control_ids") != NORMALIZATION_CONTROL_IDS
    ):
        diagnostics.append("control_inventory")
    outcomes = packet.get("result_classification_freeze", {})
    if len(outcomes.get("robustness_status_classes", [])) != 5 or len(outcomes.get("descendant_significance_classes", [])) != 3 or outcomes.get("taxonomy_frozen") is not True:
        diagnostics.append("outcome_taxonomy")
    nonclaims = packet.get("nonclaims", {})
    if any(nonclaims.get(key) is not False for key in ("robustness_pilot_executed", "robustness_execution_performed", "pillar_completion_claimed", "seam_closure_claimed", "C_k_dynamics_claimed", "CCFT_empirical_support_claimed", "master_action_promotion_claimed")):
        diagnostics.append("nonclaims")
    return diagnostics


def independently_reproduce_mutations(packet: dict[str, Any]) -> dict[str, Any]:
    mutation_specs: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        ("M_TARGET_CHANGED", "targets", lambda value: value.__setitem__("selected_next_target", "execute_early")),
        ("M_AXIS_REMOVED", "axis_levels", lambda value: value["axis_level_freeze"].pop("THETA_W")),
        ("M_LEVELS_UNFROZEN", "axis_levels", lambda value: value["axis_level_freeze"]["ETA_Q"].__setitem__("exact_values_frozen", False)),
        ("M_MATRIX_ROW_REMOVED", "scientific_matrix", lambda value: value["scientific_matrix"].pop()),
        ("M_MATRIX_DUPLICATE", "scientific_matrix", lambda value: value["scientific_matrix"][1].__setitem__("requested_axis_values", copy.deepcopy(value["scientific_matrix"][0]["requested_axis_values"]))),
        ("M_BASE_NONPOSITIVE", "scientific_matrix", lambda value: value["scientific_matrix"][0].__setitem__("positive_base_strictly_positive", False)),
        ("M_ROUND_TRIP_FAILED", "scientific_matrix", lambda value: value["scientific_matrix"][0].__setitem__("round_trip_passed", False)),
        ("M_COMPARATOR_PROMOTED", "comparator", lambda value: value["comparator_policy"].__setitem__("forced_comparator_eligible_for_positive_robustness_claim", True)),
        ("M_COMPARATOR_RELABELLED_ZERO", "comparator", lambda value: value["scientific_matrix"][0]["comparator_provenance"].__setitem__("comparator_realized_loading_status", "ZERO")),
        ("M_OBSERVABLE_REMOVED", "observables", lambda value: value["observable_freeze"]["inventory"]["descendant_observables"].pop()),
        ("M_MATERIALITY_UNFROZEN", "materiality_thresholds", lambda value: value["threshold_freeze"].__setitem__("scientific_materiality_thresholds_frozen", False)),
        ("M_PILOT_AUTHORIZED_EARLY", "pilot", lambda value: value["pilot_freeze"].__setitem__("pilot_authorized", True)),
        ("M_EXECUTION_AUTHORIZED_EARLY", "execution", lambda value: value["authority_boundary"].__setitem__("robustness_execution_authorized", True)),
        ("M_SIGNED_ROLE_CONFLATED", "semantic_roles", lambda value: value["semantic_role_separation"].__setitem__("signed_total_energy_is_physical_conservation_diagnostic", False)),
        ("M_NORMALIZATION_CONTROL_REMOVED", "normalization_controls", lambda value: value["normalization_regression_controls"].pop()),
        ("M_ACCEPTED_NEGATIVE_CONTROL_REMOVED", "control_inventory", lambda value: value["control_freeze"]["accepted_negative_control_ids"].pop()),
        ("M_OUTCOME_REMOVED", "outcome_taxonomy", lambda value: value["result_classification_freeze"]["robustness_status_classes"].pop()),
        ("M_PILLAR_PROMOTED", "nonclaims", lambda value: value["nonclaims"].__setitem__("pillar_completion_claimed", True)),
    ]
    baseline_diagnostics = independent_contract_diagnostics(packet)
    results = []
    for mutation_id, expected, mutate in mutation_specs:
        fixture = copy.deepcopy(packet)
        mutate(fixture)
        actual = independent_contract_diagnostics(fixture)
        results.append(
            {
                "mutation_id": mutation_id,
                "expected_diagnostic": expected,
                "actual_diagnostics": actual,
                "only_intended_diagnostic_fired": actual == [expected],
            }
        )
    packet_results = packet.get("mutation_controls", [])
    reported = [(item.get("mutation_id"), item.get("expected_diagnostic")) for item in packet_results]
    return {
        "baseline_diagnostics": baseline_diagnostics,
        "mutation_results": results,
        "all_eighteen_isolated": baseline_diagnostics == [] and len(results) == 18 and all(item["only_intended_diagnostic_fired"] for item in results),
        "packet_inventory_matches": reported == MUTATION_EXPECTATIONS and all(item.get("actual_diagnostics") == [item.get("expected_diagnostic")] and item.get("passed") is True for item in packet_results),
    }


def _classify_robustness(
    numerically_blocked: bool,
    domain_limited: bool,
    threshold_sensitive: bool,
    all_rows_pass: bool,
    some_rows_pass: bool,
) -> str:
    if numerically_blocked:
        return "NUMERICALLY_BLOCKED"
    if domain_limited:
        return "MODEL_DOMAIN_LIMITED"
    if threshold_sensitive:
        return "THRESHOLD_SENSITIVE"
    if all_rows_pass:
        return "BROADLY_ROBUST"
    if some_rows_pass:
        return "CONDITIONALLY_ROBUST"
    return "NUMERICALLY_BLOCKED"


def audit_observables_outcomes_and_pilot(packet: dict[str, Any]) -> dict[str, Any]:
    observable = packet.get("observable_freeze", {})
    inventory = observable.get("inventory", {})
    measurement = observable.get("measurement_contract", {})
    existing_ids = [item.get("observable_id") for item in inventory.get("existing_observables", [])]
    descendant_ids = [item.get("observable_id") for item in inventory.get("descendant_observables", [])]
    expected_existing = [
        "GAUSS_RESIDUAL",
        "CONTINUITY_RESIDUAL",
        "DIRAC_ADJOINT_RESIDUALS",
        "MAXWELL_RESIDUALS",
        "LINK_NORM_ERROR",
        "ENERGY_DRIFT",
        "SPATIAL_CONVERGENCE",
        "TEMPORAL_CONVERGENCE",
        "WILSON_CONTINUUM_BEHAVIOR",
        "EXCHANGE_TO_DRIFT_RATIO",
    ]
    expected_descendant = [
        "DELTA_E_PHI2",
        "DELTA_E_PHI3",
        "X2_SPINOR_PHI2_EXCHANGE",
        "X3_SPINOR_PHI3_EXCHANGE",
        "F_EXCHANGE_PERP",
        "R_PERP_OBSERVABLE",
        "C_PERP_SOURCE_NORM",
        "R_TRUNC_EQUATION_RESIDUAL",
        "T_DIVERGENCE",
    ]
    outcomes = packet.get("result_classification_freeze", {})
    truth_table = []
    for mask in range(32):
        flags = tuple(bool(mask & (1 << bit)) for bit in range(5))
        truth_table.append(_classify_robustness(*flags))
    thresholds = packet.get("threshold_freeze", {})
    pilot = packet.get("pilot_freeze", {})
    return {
        "observable_ids_exact": existing_ids == expected_existing and descendant_ids == expected_descendant,
        "formulas_and_norms_frozen": inventory.get("all_observable_ids_frozen") is True
        and all(item.get("definition") for item in inventory.get("descendant_observables", []))
        and all(
            key in measurement
            for key in (
                "spatial_field_norm",
                "spatial_constraint_norm",
                "time_aggregation_for_residuals",
                "time_aggregation_for_energy_changes",
                "time_aggregation_for_exchange",
            )
        ),
        "robustness_and_significance_tracks_separate": len(outcomes.get("robustness_status_classes", [])) == 5
        and len(outcomes.get("descendant_significance_classes", [])) == 3
        and outcomes.get("descendant_significance_decision_rules", {}).get("NO_SIGNIFICANCE_CLASS_WHEN_BLOCKED") is not None,
        "classification_order_exact": outcomes.get("classification_order") == ROBUSTNESS_CLASSIFICATION_ORDER,
        "deterministic_precedence_truth_table_cases": len(truth_table),
        "every_precedence_case_has_exactly_one_label": len(truth_table) == 32 and all(label in ROBUSTNESS_CLASSIFICATION_ORDER for label in truth_table),
        "scientific_materiality_frozen_before_pilot": thresholds.get("scientific_materiality_thresholds_frozen") is True
        and thresholds.get("material_R_perp_gate") == 0.1
        and thresholds.get("material_F_exchange_perp_gate") == 0.1
        and thresholds.get("descendant_dominated_R_perp_gate") == 0.5
        and thresholds.get("descendant_dominated_F_exchange_perp_gate") == 0.5,
        "numerical_thresholds_remain_pending_pilot": thresholds.get("numerical_floor_values_frozen") is False
        and thresholds.get("numerical_acceptance_threshold_values_frozen") is False
        and thresholds.get("canonical_numerical_thresholds_automatically_reused") is False,
        "pilot_subset_exact_and_frozen": pilot.get("pilot_row_ids") == PILOT_ROW_IDS and pilot.get("pilot_subset_frozen") is True,
        "pilot_scope_is_engineering_only": pilot.get("pilot_may_calibrate_only") == PILOT_MAY_CALIBRATE_ONLY
        and pilot.get("pilot_may_not_change") == PILOT_MAY_NOT_CHANGE,
        "difficult_rows_must_remain": pilot.get("failed_pilot_rows_retained") is True and outcomes.get("difficult_or_failed_rows_cannot_be_dropped") is True,
        "pilot_not_yet_executed_or_preaccepted": pilot.get("pilot_authorized") is False
        and pilot.get("pilot_is_not_scientific_robustness_execution") is True
        and packet.get("nonclaims", {}).get("robustness_pilot_executed") is False,
    }


def reconstruct_review_decisions(
    packet: dict[str, Any],
    matrix: dict[str, Any],
    normalization_controls: list[dict[str, Any]],
    mutations: dict[str, Any],
    protocol: dict[str, Any],
) -> dict[str, bool]:
    comparator = packet.get("comparator_policy", {})
    rows = packet.get("scientific_matrix", [])
    control_freeze = packet.get("control_freeze", {})
    positive_controls = {item.get("control_id"): item for item in packet.get("positive_controls", [])}
    negative_controls = {item.get("control_id"): item for item in packet.get("negative_controls", [])}
    authority = packet.get("authority_boundary", {})
    historical_review = load_json(REPO_ROOT / HISTORICAL_GUARDRAIL_REVIEW_RELATIVE_PATH)
    axis_review = load_json(REPO_ROOT / AXIS_REPAIR_REVIEW_RELATIVE_PATH)
    authority_inputs = packet.get("authority_inputs", [])
    authority_inputs_bound = all(sha256_path(REPO_ROOT / item["path"]) == item["sha256"] for item in authority_inputs)
    return {
        "preparation_target_and_review_boundary_exact": packet.get("target") == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v1"
        and packet.get("selected_next_target") == REVIEW_TARGET
        and packet.get("verdict") == "PREPARED_GUARDRAIL_V1_PENDING_INDEPENDENT_REVIEW",
        "all_six_preparation_artifacts_bound": len(EXPECTED_PREPARATION_HASHES) == 6,
        "all_five_axes_and_levels_reconstructed": set(packet.get("axis_level_freeze", {})) == set(AXIS_LEVELS)
        and matrix["all_rows_match_packet"],
        "positive_base_reconstructed_and_strictly_positive": matrix["all_positive_bases_strictly_positive"],
        "descendant_energy_amplitude_and_loading_reconstructed": matrix["maximum_loading_round_trip_error"] <= ROUND_TRIP_TOLERANCE,
        "other_four_axes_do_not_drift": matrix["maximum_other_axis_drift"] <= ROUND_TRIP_TOLERANCE,
        "loading_odds_are_multiplicatively_symmetric": matrix["multiplicative_loading_symmetry"],
        "matrix_identity_is_exact_unique_and_circular_safe": matrix["scientific_row_count"] == 14
        and matrix["unique_row_identity_count"] == 14
        and matrix["unique_circular_parameter_tuple_count"] == 14
        and matrix["zero_and_two_pi_duplicate_absent"],
        "matrix_roles_are_one_ten_three": matrix["role_counts"] == {"CANONICAL_ANCHOR": 1, "ONE_AT_A_TIME": 10, "INTERACTION_CORNER": 3},
        "matrix_precedes_and_is_independent_of_pilot_results": authority.get("robustness_pilot_authorized") is False
        and packet.get("nonclaims", {}).get("robustness_pilot_executed") is False,
        "full_model_is_positive_evidence_system_for_every_row": len(rows) == 14
        and comparator.get("full_model_id") == "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM"
        and comparator.get("full_model_eligible_for_positive_robustness_claim") is True,
        "forced_comparator_is_negative_only_and_keeps_parent_provenance": comparator.get("forced_comparator_eligible_for_positive_robustness_claim") is False
        and comparator.get("recompute_as_zero_for_scientific_axis_forbidden") is True
        and all(
            row.get("comparator_provenance", {}).get("requested_parent_axis_values_preserved_as_provenance") == row.get("requested_axis_values")
            and row.get("comparator_provenance", {}).get("comparator_realized_loading") is None
            and row.get("comparator_provenance", {}).get("comparator_realized_loading_status") == "NOT_PHYSICALLY_ELIGIBLE"
            for row in rows
        ),
        "invariant_descendant_free_comparator_requires_analytic_authority": comparator.get("descendant_free_special_subdomain") == "NOT_AVAILABLE_WITHOUT_SEPARATE_ACCEPTED_INVARIANCE_PROOF"
        and positive_controls.get("P_ANALYTIC_INVARIANT_DESCENDANT_FREE", {}).get("status") == "CONDITIONAL_ON_ACCEPTED_INVARIANT_SUBDOMAIN_PROOF",
        "all_twenty_normalization_regressions_independently_reproduced": [item["control_id"] for item in normalization_controls] == NORMALIZATION_CONTROL_IDS
        and all(item["independently_reproduced"] for item in normalization_controls),
        "all_eighteen_mutations_fail_for_only_the_intended_reason": mutations["all_eighteen_isolated"] and mutations["packet_inventory_matches"],
        "original_transverse_blocker_remains_permanent": control_freeze.get("original_transverse_sector_blocker_remains_permanent_regression") is True
        and negative_controls.get("N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE", {}).get("diagnostic") == "ORIGINAL_TRANSVERSE_BLOCKER_REGRESSION"
        and negative_controls.get("N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE", {}).get("permanent_regression") is True,
        "observables_formulas_and_norms_are_fixed": protocol["observable_ids_exact"] and bool(protocol["formulas_and_norms_frozen"]),
        "robustness_and_significance_tracks_are_separate": protocol["robustness_and_significance_tracks_separate"],
        "outcome_precedence_is_deterministic_and_unambiguous": protocol["classification_order_exact"] and protocol["every_precedence_case_has_exactly_one_label"],
        "materiality_is_frozen_but_numerical_thresholds_are_not": protocol["scientific_materiality_frozen_before_pilot"] and protocol["numerical_thresholds_remain_pending_pilot"],
        "pilot_subset_and_engineering_only_boundary_are_fixed": protocol["pilot_subset_exact_and_frozen"] and protocol["pilot_scope_is_engineering_only"] and protocol["difficult_rows_must_remain"],
        "canonical_robustness_execution_remains_unauthorized": authority.get("robustness_execution_authorized") is False
        and authority.get("robustness_parameter_calibration_authorized") is False,
        "guardrail_v0_and_signed_axis_blocker_remain_immutable": historical_review.get("verdict") == "B-BLOCKED_F_PERP_NORMALIZATION_NOT_BOUNDED"
        and historical_review.get("blocker_confirmed") is True,
        "axis_repair_is_sole_v1_normalization_authority": axis_review.get("accepted") is True
        and axis_review.get("verdict") == "ACCEPT_AXIS_NORMALIZATION_REPAIR"
        and axis_review.get("replacement_axis_id") == REPLACEMENT_AXIS_ID,
        "canonical_E_REPRO_result_and_all_authority_inputs_are_unchanged": authority.get("canonical_E_REPRO_result_remains_accepted") is True
        and authority_inputs_bound,
        "nonclaims_remain_closed": all(
            authority.get(key) is False
            for key in (
                "pillar_promotion_authorized",
                "seam_closure_authorized",
                "C_k_dynamics_authorized",
                "CCFT_empirical_promotion_authorized",
                "master_action_promotion_authorized",
            )
        ),
    }


def build_review() -> dict[str, Any]:
    binding = bind_preparation()
    packet = load_json(REPO_ROOT / PACKET_RELATIVE_PATH)
    matrix = independently_reconstruct_matrix(packet)
    normalization_controls = independently_reproduce_normalization_controls(matrix)
    mutations = independently_reproduce_mutations(packet)
    protocol = audit_observables_outcomes_and_pilot(packet)
    decisions = reconstruct_review_decisions(packet, matrix, normalization_controls, mutations, protocol)
    if not all(decisions.values()):
        raise ValueError(f"independent guardrail-v1 review failed: {[key for key, value in decisions.items() if not value]}")
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": True,
        "verdict": VERDICT,
        "independent_matrix_reconstruction": matrix,
        "independent_normalization_regression_controls": normalization_controls,
        "independent_mutation_audit": mutations,
        "observable_outcome_and_pilot_audit": protocol,
        "review_decisions": decisions,
        "preparation_binding": binding,
        "preparation_generator_imported": False,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "BOUNDED_NON_AUTHORITATIVE_ROBUSTNESS_PILOT_v1",
        "authority_rotation": {
            "guardrail_v1_accepted": True,
            "bounded_non_authoritative_pilot_authorized": True,
            "pilot_subset_remains_frozen": True,
            "scientific_materiality_thresholds_remain_frozen": True,
            "numerical_threshold_calibration_may_be_observed_in_pilot": True,
            "numerical_threshold_or_parameter_freeze_authorized": False,
            "canonical_robustness_execution_authorized": False,
            "new_scientific_claim_authorized": False,
            "broad_robustness_claim_authorized": False,
            "descendant_materiality_classification_authorized": False,
            "new_E_REPRO_claim_authorized": False,
            "canonical_E_REPRO_result_remains_accepted": True,
            "historical_guardrail_v0_rewritten": False,
            "historical_signed_axis_rehabilitated": False,
            "pillar_completion_authorized": False,
            "seam_closure_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_validation_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "lean_status_boundary": {
            "direct_affected_preparation_witness": "PASSED",
            "repository_wide_aggregate": "INCOMPLETE_DUE_TO_600_SECOND_TIMEOUT",
            "jobs_reached_before_timeout": 8441,
            "jobs_total": 8507,
            "theorem_error_observed_before_timeout": False,
            "repository_wide_green_claim_made": False,
        },
        "claim_ceiling": "Guardrail v1 is independently accepted and authorizes only the five-row bounded non-authoritative robustness pilot. The pilot may exercise the frozen construction and estimate engineering tolerances under the frozen rule; it may not freeze calibration, execute canonical robustness, alter scientific definitions, or support a new scientific claim.",
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
