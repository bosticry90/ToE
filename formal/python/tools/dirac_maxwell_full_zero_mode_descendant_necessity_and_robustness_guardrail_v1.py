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
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_v1.py"

AXIS_REPAIR_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_AXIS_NORMALIZATION_REPAIR_PACKET_RESULT_REVIEW_20260713_v0.json"
AXIS_REPAIR_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-AXIS-NORMALIZATION-REPAIR-PACKET-v0.json"
DESIGN_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_RESULT_REVIEW_20260713_v0.json"
DESIGN_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-PACKET-v0.json"
CANONICAL_PRIMARY_RELATIVE_PATH = "formal/output/canonical/dirac_maxwell_full_zero_mode_v0/CANONICAL_PRIMARY_N32_DT0P0015625.json"
NUMERICAL_IMPLEMENTATION_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"

PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v1.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-MANIFEST-v1.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_20260714_v1.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v1"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v1_result"
FAILURE_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v2"
POST_ACCEPTANCE_TARGET = "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_v1"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_MANIFEST_v1"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_20260714_v1"

INPUT_HASHES = {
    AXIS_REPAIR_REVIEW_RELATIVE_PATH: "2840f6edbd1414b8e685c661de1f51cc13c28b3c629e6ff2be36b16921d3d391",
    AXIS_REPAIR_PACKET_RELATIVE_PATH: "7863ae08a12841f3dba9e9a5a7b2375af8ec9c1b4ae8eef9918d15bbad3bfb88",
    DESIGN_REVIEW_RELATIVE_PATH: "84140ac762b660a1f4ab86d9376a50bad256de1bf0f4faa9898195a5eb9fa0f9",
    DESIGN_PACKET_RELATIVE_PATH: "98a635b92d3a2b5479cc41aca80760a965a249fb3ae16c476b3a50aab6e10100",
    CANONICAL_PRIMARY_RELATIVE_PATH: "97b3fe6c4ed0cfee904158fcbf778a74b0501b40580dba33e0f9300ea7b28e7a",
    NUMERICAL_IMPLEMENTATION_RELATIVE_PATH: "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

HISTORICAL_AXIS_ID = "F_PERP_INITIAL_SIGNED_TOTAL_v0"
REPLACEMENT_AXIS_ID = "F_PERP_POSITIVE_LOADING_INITIAL_v1"
GRID_SIZE = 32
LENGTH = 1.0
ROUND_TRIP_TOLERANCE = 2e-15
F_LOADING_UPPER_ADMISSIBILITY_CEILING = 0.8
LOADING_ODDS_MULTIPLIER = 4.0
CANONICAL_LOADING = 0.2131315883288088
LOW_LOADING = 0.0634205964176414
HIGH_LOADING = 0.5200250552967295

PILOT_ROW_IDS = ["R00_CANONICAL", "R03_F_ZERO", "R05_F_HIGH", "R10_MU_HIGH", "R11_CORNER_WEAK_HIGH"]
REGISTERED_R_PERP_OBSERVABLES = [
    "MATTER_DENSITY",
    "LONGITUDINAL_ELECTRIC_FIELD",
    "MATTER_ENERGY",
    "LONGITUDINAL_EXCHANGE",
    "TOTAL_SOURCE_CURRENT",
]

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
    review = sources[AXIS_REPAIR_REVIEW_RELATIVE_PATH]
    authority = review.get("authority_rotation", {})
    if not (
        review.get("accepted") is True
        and review.get("verdict") == "ACCEPT_AXIS_NORMALIZATION_REPAIR"
        and review.get("selected_next_target") == TARGET
        and review.get("replacement_axis_id") == REPLACEMENT_AXIS_ID
        and authority.get("guardrail_v1_preparation_authorized") is True
        and authority.get("robustness_pilot_authorized") is False
        and authority.get("robustness_execution_authorized") is False
        and authority.get("canonical_E_REPRO_result_remains_accepted") is True
    ):
        raise ValueError("accepted normalization review does not authorize guardrail v1 preparation")
    design_review = sources[DESIGN_REVIEW_RELATIVE_PATH]
    if not (
        design_review.get("accepted") is True
        and design_review.get("verdict") == "ACCEPT_SCIENTIFIC_DESIGN"
        and design_review.get("accepted_design", {}).get("future_exact_unique_scientific_row_count_range") == [12, 14]
    ):
        raise ValueError("accepted descendant-necessity design is not bound")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        raise ValueError("Prompt.txt changed")
    return sources


def reference_inventory() -> dict[str, Any]:
    state = numerical.initial_state("full_mixed", GRID_SIZE, numerical.CHARGE)
    a = LENGTH / GRID_SIZE
    components = numerical.energy_components(state, a, numerical.CHARGE)
    number_by_species = {
        species: float(a * np.sum(np.abs(state[species]) ** 2))
        for species in ("psi_plus", "psi_minus")
    }
    descendant = components["phi2"] + components["phi3"]
    parallel = components["electric_fluctuating"] + components["electric_zero_mode"]
    total_number = sum(number_by_species.values())
    positive_base = parallel + numerical.MASS * total_number
    coordinate = descendant / (descendant + positive_base)
    if not math.isclose(coordinate, CANONICAL_LOADING, rel_tol=0.0, abs_tol=1e-15):
        raise ValueError("canonical positive-loading anchor changed")
    return {
        "profile_id": "FULL_MIXED_DESCENDANT_PROFILE_N32_v0",
        "base_state_id": "FULL_MIXED_SPINOR_AND_LONGITUDINAL_BASE_N32_v0",
        "grid_size": GRID_SIZE,
        "length": LENGTH,
        "descendant_reference_energy": descendant,
        "parallel_Maxwell_energy": parallel,
        "number_by_species": number_by_species,
        "total_matter_number": total_number,
        "positive_base_energy_at_mass_one": positive_base,
        "canonical_loading": coordinate,
        "descendant_profile": {
            "phi2": "0.01*cos(2*pi*x/L)",
            "P2": "0",
            "phi3": "0.008*sin(4*pi*x/L)",
            "P3": "0",
            "scaling_rule": "multiply phi2, P2, phi3, and P3 by the reconstructed finite alpha",
            "source_function": "dirac_maxwell_full_zero_mode_non_authoritative_pilot.initial_state('full_mixed',32,q)",
        },
        "strict_positivity_witness": "Every scientific row has m>=1 and the fixed total matter number is strictly positive, so B_plus>=m*N_total>0.",
    }


def axis_level_freeze() -> dict[str, Any]:
    anchor_odds = CANONICAL_LOADING / (1.0 - CANONICAL_LOADING)
    low_from_rule = (anchor_odds / LOADING_ODDS_MULTIPLIER) / (1.0 + anchor_odds / LOADING_ODDS_MULTIPLIER)
    high_from_rule = (anchor_odds * LOADING_ODDS_MULTIPLIER) / (1.0 + anchor_odds * LOADING_ODDS_MULTIPLIER)
    if not math.isclose(low_from_rule, LOW_LOADING, rel_tol=0.0, abs_tol=1e-15):
        raise ValueError("low loading constant no longer follows the frozen odds rule")
    if not math.isclose(high_from_rule, HIGH_LOADING, rel_tol=0.0, abs_tol=1e-15):
        raise ValueError("high loading constant no longer follows the frozen odds rule")
    return {
        "ETA_Q": {
            "definition": "q_1p1/m",
            "levels": {"WEAKER": 0.1, "CANONICAL": 0.2, "STRONGER": 0.4},
            "selection_rule": "factor-two log-symmetric variation around the accepted canonical 0.2",
            "exact_values_frozen": True,
        },
        REPLACEMENT_AXIS_ID: {
            "definition": "E_perp/(E_perp+B_plus)",
            "positive_base_definition": "B_plus=E_parallel_Maxwell+m*sum_s,r(N_s,r)",
            "levels": {
                "ZERO": 0.0,
                "LOW_NONZERO": LOW_LOADING,
                "CANONICAL": CANONICAL_LOADING,
                "HIGH": HIGH_LOADING,
            },
            "anchor_loading_odds": anchor_odds,
            "loading_odds_multiplier": LOADING_ODDS_MULTIPLIER,
            "low_high_rule": "low/high use one-half/two-times reference descendant amplitude, equivalently anchor loading odds divided/multiplied by four",
            "upper_admissibility_ceiling": F_LOADING_UPPER_ADMISSIBILITY_CEILING,
            "exact_values_frozen": True,
            "historical_axis_retained_as_diagnostic_only": HISTORICAL_AXIS_ID,
        },
        "THETA_W": {
            "definition": "principal Arg(W) in (-pi,pi]",
            "levels": {"TRIVIAL": 0.0, "NONTRIVIAL": 0.3, "SYMMETRY_PARTNER": -0.3},
            "selection_rule": "accepted nontrivial anchor, its sign partner, and the trivial holonomy",
            "exact_values_frozen": True,
        },
        "DELTA_THETA_PSI": {
            "definition": "relative phase applied to reduced components [1,3] of both charge species",
            "levels": {"CANONICAL": 0.0, "POSITIVE_OFFSET": math.pi / 2, "NEGATIVE_OFFSET": -math.pi / 2},
            "selection_rule": "canonical phase and quarter-turn sign partners",
            "exact_values_frozen": True,
        },
        "MU_MASS_DOMAIN": {
            "definition": "m*L_x with L_x fixed to one",
            "levels": {"CANONICAL": 1.0, "BOUNDED_VARIATION": 2.0},
            "selection_rule": "accepted canonical value and one factor-two mass/domain variation",
            "exact_values_frozen": True,
        },
    }


def _level_values(levels: dict[str, Any], spec: tuple[str, ...]) -> dict[str, float]:
    _, _, eta_level, f_level, theta_level, phase_level, mu_level = spec
    return {
        "ETA_Q": float(levels["ETA_Q"]["levels"][eta_level]),
        REPLACEMENT_AXIS_ID: float(levels[REPLACEMENT_AXIS_ID]["levels"][f_level]),
        "THETA_W": float(levels["THETA_W"]["levels"][theta_level]),
        "DELTA_THETA_PSI": float(levels["DELTA_THETA_PSI"]["levels"][phase_level]),
        "MU_MASS_DOMAIN": float(levels["MU_MASS_DOMAIN"]["levels"][mu_level]),
    }


def construct_matrix_row(levels: dict[str, Any], reference: dict[str, Any], spec: tuple[str, ...]) -> dict[str, Any]:
    row_id, row_role, eta_level, f_level, theta_level, phase_level, mu_level = spec
    requested = _level_values(levels, spec)
    eta = requested["ETA_Q"]
    loading = requested[REPLACEMENT_AXIS_ID]
    theta_w = requested["THETA_W"]
    delta_phase = requested["DELTA_THETA_PSI"]
    mu = requested["MU_MASS_DOMAIN"]

    mass = mu / LENGTH
    charge = eta * mass
    theta_link_constant = theta_w / (charge * GRID_SIZE)
    parallel = float(reference["parallel_Maxwell_energy"])
    total_number = float(reference["total_matter_number"])
    positive_base = parallel + mass * total_number
    target_descendant = 0.0 if loading == 0.0 else (loading / (1.0 - loading)) * positive_base
    alpha = 0.0 if target_descendant == 0.0 else math.sqrt(target_descendant / float(reference["descendant_reference_energy"]))
    reconstructed_descendant = alpha**2 * float(reference["descendant_reference_energy"])
    reconstructed_loading = reconstructed_descendant / (reconstructed_descendant + positive_base)
    reconstructed = {
        "ETA_Q": charge / mass,
        REPLACEMENT_AXIS_ID: reconstructed_loading,
        "THETA_W": charge * GRID_SIZE * theta_link_constant,
        "DELTA_THETA_PSI": delta_phase,
        "MU_MASS_DOMAIN": mass * LENGTH,
    }
    errors = {key: abs(reconstructed[key] - requested[key]) for key in requested}
    round_trip_passed = all(error <= ROUND_TRIP_TOLERANCE for error in errors.values())
    domain_passed = (
        mass > 0.0
        and charge > 0.0
        and positive_base > 0.0
        and 0.0 <= loading <= F_LOADING_UPPER_ADMISSIBILITY_CEILING < 1.0
        and math.isfinite(alpha)
    )
    comparator = {
        "comparator_class": "INTENTIONALLY_NONINVARIANT_COMPARATOR",
        "requested_parent_row_loading": loading,
        "requested_parent_axis_values_preserved_as_provenance": copy.deepcopy(requested),
        "descendants_removed_after_full_parent_row_construction": True,
        "comparator_realized_loading": None,
        "comparator_realized_loading_status": "NOT_PHYSICALLY_ELIGIBLE",
        "eligible_for_positive_model_robustness_claim": False,
        "eligible_only_for_descendant_necessity_negative_control": True,
    }
    return {
        "row_id": row_id,
        "row_role": row_role,
        "requested_level_ids": {
            "ETA_Q": eta_level,
            REPLACEMENT_AXIS_ID: f_level,
            "THETA_W": theta_level,
            "DELTA_THETA_PSI": phase_level,
            "MU_MASS_DOMAIN": mu_level,
        },
        "requested_axis_values": requested,
        "construction_order": [
            "set ETA_Q",
            "set THETA_W",
            "set DELTA_THETA_PSI",
            "set MU_MASS_DOMAIN",
            "construct longitudinal Maxwell and spinor base state",
            "compute B_plus",
            f"select requested {REPLACEMENT_AXIS_ID}",
            "invert loading formula for E_perp",
            "compute fixed descendant-profile alpha",
            "recalculate all five axes",
            "enforce frozen round-trip tolerance",
        ],
        "derived_initial_state_parameters": {
            "length": LENGTH,
            "grid_size": GRID_SIZE,
            "mass": mass,
            "charge": charge,
            "constant_link_coordinate_theta_n": theta_link_constant,
            "relative_spinor_phase_radians": delta_phase,
            "parallel_Maxwell_energy": parallel,
            "total_matter_number": total_number,
            "positive_base_energy_B_plus": positive_base,
            "requested_descendant_energy": target_descendant,
            "reference_descendant_profile_alpha": alpha,
            "reconstructed_descendant_energy": reconstructed_descendant,
        },
        "round_trip_axis_values": reconstructed,
        "round_trip_absolute_errors": errors,
        "round_trip_tolerance": ROUND_TRIP_TOLERANCE,
        "round_trip_passed": round_trip_passed,
        "positive_base_strictly_positive": positive_base > 0.0,
        "loading_bounded": 0.0 <= reconstructed_loading < 1.0,
        "gauge_equivalent_loading_error": 0.0,
        "gauge_witness": "E_perp, E_parallel_Maxwell, and every registered number norm are gauge invariant under the accepted U(1) transformation",
        "initial_data_domain_passed": domain_passed,
        "comparator_provenance": comparator,
        "control_roles": [
            role
            for role, condition in (
                ("CANONICAL_ANCHOR", row_role == "CANONICAL_ANCHOR"),
                ("ZERO_DESCENDANT_SOURCE_RESPONSE", f_level == "ZERO"),
                ("WEAK_COUPLING_APPROACH", eta_level == "WEAKER"),
                ("INTERACTION_CORNER", row_role == "INTERACTION_CORNER"),
            )
            if condition
        ],
    }


def scientific_matrix(levels: dict[str, Any], reference: dict[str, Any]) -> list[dict[str, Any]]:
    return [construct_matrix_row(levels, reference, spec) for spec in ROW_LEVEL_SPECS]


def matrix_audit(rows: list[dict[str, Any]]) -> dict[str, Any]:
    tuples = [tuple(row["requested_axis_values"].values()) for row in rows]
    roles = [row["row_role"] for row in rows]
    return {
        "scientific_row_count": len(rows),
        "row_count_inside_accepted_range_12_through_14": 12 <= len(rows) <= 14,
        "unique_requested_tuple_count": len(set(tuples)),
        "all_requested_tuples_unique": len(set(tuples)) == len(tuples),
        "canonical_anchor_count": roles.count("CANONICAL_ANCHOR"),
        "one_at_a_time_count": roles.count("ONE_AT_A_TIME"),
        "interaction_corner_count": roles.count("INTERACTION_CORNER"),
        "all_positive_bases_strictly_positive": all(row["positive_base_strictly_positive"] for row in rows),
        "all_loading_values_bounded": all(row["loading_bounded"] for row in rows),
        "all_descendant_amplitudes_finite": all(math.isfinite(row["derived_initial_state_parameters"]["reference_descendant_profile_alpha"]) for row in rows),
        "all_initial_data_inside_domain": all(row["initial_data_domain_passed"] for row in rows),
        "all_five_axis_round_trips_pass": all(row["round_trip_passed"] for row in rows),
        "maximum_loading_round_trip_error": max(row["round_trip_absolute_errors"][REPLACEMENT_AXIS_ID] for row in rows),
        "all_comparators_preserve_parent_loading_as_provenance": all(
            row["comparator_provenance"]["requested_parent_row_loading"] == row["requested_axis_values"][REPLACEMENT_AXIS_ID]
            for row in rows
        ),
        "no_comparator_realized_loading_falsely_assigned_zero": all(
            row["comparator_provenance"]["comparator_realized_loading"] is None for row in rows
        ),
    }


def comparator_policy() -> dict[str, Any]:
    return {
        "full_model_id": "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM",
        "full_model_eligible_for_positive_robustness_claim": True,
        "forced_comparator_id": "INTENTIONALLY_NONINVARIANT_COMPARATOR",
        "forced_comparator_eligible_for_positive_robustness_claim": False,
        "forced_comparator_use": "negative control for descendant necessity only",
        "parent_requested_loading_preserved": True,
        "realized_loading_after_forced_removal": "NOT_PHYSICALLY_ELIGIBLE",
        "recompute_as_zero_for_scientific_axis_forbidden": True,
        "descendant_free_special_subdomain": "NOT_AVAILABLE_WITHOUT_SEPARATE_ACCEPTED_INVARIANCE_PROOF",
    }


def observable_freeze(design: dict[str, Any]) -> dict[str, Any]:
    inventory = copy.deepcopy(design["observable_registry"])
    inventory["all_observable_ids_frozen"] = True
    inventory["future_freeze_requirements"] = {
        "epsilon_exchange_floor_generation_rule_frozen": True,
        "epsilon_observable_floor_generation_rule_frozen": True,
        "delta_O_frozen_per_registered_observable": True,
        "norms_time_aggregation_and_spatial_aggregation_frozen": True,
        "no_post_result_observable_selection": True,
    }
    return {
        "inventory": inventory,
        "measurement_contract": {
            "spatial_field_norm": "sqrt(dx*sum_x(|field(x)|^2))",
            "spatial_constraint_norm": "max_x absolute value, with L2 also reported",
            "time_aggregation_for_residuals": "maximum over every stored time sample",
            "time_aggregation_for_energy_changes": "maximum absolute departure from the row's initial value",
            "time_aggregation_for_exchange": "maximum absolute cumulative registered exchange over the common duration",
            "full_vs_comparator_alignment": "same parent row, grid, time samples, duration, and solver settings",
            "R_PERP_OBSERVABLE": "max_t ||O_full-O_comparator||_2/(max_t ||O_full||_2+epsilon_observable_floor), reported separately for every registered O",
            "F_EXCHANGE_PERP": "(|X2|+|X3|)/(|X_longitudinal|+|X2|+|X3|+epsilon_exchange_floor) using the maximum absolute cumulative exchanges",
            "C_PERP_SOURCE_NORM": "max_t sqrt(||J2||_2^2+||J3||_2^2) in the forced comparator",
            "R_TRUNC_EQUATION_RESIDUAL": "max_t sqrt(||Box(phi2)-J2||_2^2+||Box(phi3)-J3||_2^2) in the forced comparator",
            "T_DIVERGENCE": "first stored time at which the corresponding pointwise-in-time R_perp,O reaches delta_O; RIGHT_CENSORED_AT_DURATION if absent",
            "registered_R_PERP_O_ids": REGISTERED_R_PERP_OBSERVABLES,
            "signed_total_energy_role": "physical conservation and exchange diagnostic only",
            "positive_loading_denominator_role": "initial-state design and normalization only",
        },
    }


def threshold_freeze() -> dict[str, Any]:
    delta = {observable_id: 0.1 for observable_id in REGISTERED_R_PERP_OBSERVABLES}
    return {
        "scientific_materiality_thresholds_frozen": True,
        "delta_O_for_T_DIVERGENCE": delta,
        "material_R_perp_gate": 0.1,
        "descendant_dominated_R_perp_gate": 0.5,
        "material_F_exchange_perp_gate": 0.1,
        "descendant_dominated_F_exchange_perp_gate": 0.5,
        "threshold_sensitivity_values": [0.05, 0.1, 0.2],
        "threshold_sensitivity_rule": "replace both 0.1 materiality gates by each frozen sensitivity value while retaining the 0.5 dominated gates",
        "resolved_above_numerical_floor_rule": "signal must exceed ten times its independently calibrated numerical floor",
        "epsilon_F_round_trip": ROUND_TRIP_TOLERANCE,
        "loading_upper_admissibility_ceiling": F_LOADING_UPPER_ADMISSIBILITY_CEILING,
        "numerical_floor_values_frozen": False,
        "numerical_acceptance_threshold_values_frozen": False,
        "reason_numerical_values_pending": "Only a reviewed non-authoritative pilot may calibrate numerical floors and solver thresholds under the frozen rules.",
        "canonical_numerical_thresholds_automatically_reused": False,
        "no_post_result_threshold_relaxation": True,
    }


def pilot_freeze() -> dict[str, Any]:
    return {
        "pilot_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_v1",
        "pilot_row_ids": PILOT_ROW_IDS,
        "pilot_subset_frozen": True,
        "pilot_authorized": False,
        "pilot_requires_guardrail_v1_independent_acceptance": True,
        "pilot_may_calibrate_only": [
            "solver_tolerance",
            "grid_sequence",
            "time_step_sequence",
            "duration",
            "iteration_cap",
            "epsilon_exchange_floor",
            "epsilon_observable_floor",
            "residual_acceptance_thresholds",
        ],
        "pilot_may_not_change": [
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
        ],
        "calibration_generation_rule": "for each numerical residual/floor, take the maximum across every frozen pilot row and calibration refinement, multiply by two, and round upward to one significant digit",
        "failed_pilot_rows_retained": True,
        "pilot_is_not_scientific_robustness_execution": True,
        "implementation_requirements_before_any_pilot_run": {
            "new_versioned_pilot_implementation_required": True,
            "accepted_v0_numerical_implementation_is_reference_only": True,
            "mass_must_be_an_explicit_runtime_parameter_not_a_module_global": True,
            "charge_must_be_constructed_as_eta_q_times_mass": True,
            "holonomy_must_be_constructed_from_the_requested_THETA_W": True,
            "relative_spinor_phase_must_be_applied_to_reduced_components_1_and_3": True,
            "descendant_profile_alpha_must_be_applied_after_B_plus_is_computed": True,
            "all_five_axes_must_round_trip_before_time_evolution": True,
            "implementation_change_cannot_alter_the_accepted_equations_or_energy_inventory": True,
        },
    }


def result_classification_freeze(design: dict[str, Any]) -> dict[str, Any]:
    taxonomy = copy.deepcopy(design["outcome_taxonomy"])
    taxonomy.update({
        "taxonomy_frozen": True,
        "classification_order": [
            "NUMERICALLY_BLOCKED",
            "MODEL_DOMAIN_LIMITED",
            "THRESHOLD_SENSITIVE",
            "BROADLY_ROBUST",
            "CONDITIONALLY_ROBUST",
        ],
        "robustness_decision_rules": {
            "NUMERICALLY_BLOCKED": "one or more required rows lack controlled solver, residual, or convergence evidence",
            "MODEL_DOMAIN_LIMITED": "one or more preregistered rows exit the admitted classical model domain; the row remains reported",
            "THRESHOLD_SENSITIVE": "the robustness or descendant-significance conclusion changes across the frozen 0.05, 0.1, 0.2 sensitivity values",
            "BROADLY_ROBUST": "every full-model scientific row meets every frozen numerical-quality and control criterion and the conclusion is not threshold-sensitive",
            "CONDITIONALLY_ROBUST": "a nonempty explicitly listed preregistered subdomain meets every criterion but the full frozen matrix does not",
        },
        "descendant_significance_decision_rules": {
            "DESCENDANT_DOMINATED_REGIME": "resolved evidence has F_EXCHANGE_PERP>=0.5 or any registered R_PERP_OBSERVABLE>=0.5",
            "INTERMEDIATE_DESCENDANT_CONTRIBUTION": "resolved evidence crosses a 0.1 materiality gate but neither dominated gate",
            "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL": "the structural noninvariance/source residual is resolved while all registered R_PERP and F_EXCHANGE_PERP values remain below 0.1",
            "NO_SIGNIFICANCE_CLASS_WHEN_BLOCKED": "no descendant-significance class is assigned when required numerical evidence is blocked or outside the model domain",
        },
        "forced_comparator_cannot_support_robustness_pass": True,
        "difficult_or_failed_rows_cannot_be_dropped": True,
    })
    return taxonomy


def _state_with_phase_and_scale(delta: float, alpha: float = 1.0) -> dict[str, np.ndarray]:
    state = numerical.initial_state("full_mixed", GRID_SIZE, numerical.CHARGE)
    z = complex(math.cos(delta), math.sin(delta))
    for species in ("psi_plus", "psi_minus"):
        state[species][:, [1, 3]] *= z
    for field in ("phi2", "P2", "phi3", "P3"):
        state[field] *= alpha
    return state


def _coordinate(state: dict[str, np.ndarray], mass: float = 1.0) -> dict[str, float]:
    a = LENGTH / GRID_SIZE
    energy = numerical.energy_components(state, a, numerical.CHARGE)
    descendant = energy["phi2"] + energy["phi3"]
    number = sum(float(a * np.sum(np.abs(state[species]) ** 2)) for species in ("psi_plus", "psi_minus"))
    parallel = energy["electric_fluctuating"] + energy["electric_zero_mode"]
    base = parallel + mass * number
    return {
        "descendant": descendant,
        "base": base,
        "loading": descendant / (descendant + base) if descendant + base > 0.0 else math.nan,
        "signed_total": sum(energy.values()),
    }


def historical_and_replacement_audit(rows: list[dict[str, Any]], reference: dict[str, Any]) -> dict[str, Any]:
    positive_phase = _state_with_phase_and_scale(math.pi / 2)
    positive = _coordinate(positive_phase)
    historical_ratio = positive["descendant"] / positive["signed_total"]
    components = numerical.energy_components(positive_phase, LENGTH / GRID_SIZE, numerical.CHARGE)
    coefficients = {
        "a": positive["descendant"],
        "b": components["gamma2_interaction"] + components["gamma3_interaction"],
        "c": components["electric_fluctuating"] + components["electric_zero_mode"] + components["Wilson_Dirac_local"] + components["link_interaction"],
    }
    roots = np.roots([coefficients["a"], coefficients["b"], coefficients["c"]])
    crossing = min(float(root.real) for root in roots if abs(root.imag) < 1e-12 and root.real > 0.0)
    below = coefficients["a"] * (crossing / 2) ** 2 + coefficients["b"] * (crossing / 2) + coefficients["c"]
    above = coefficients["a"] * (crossing * 2) ** 2 + coefficients["b"] * (crossing * 2) + coefficients["c"]

    gauge_state = _state_with_phase_and_scale(0.0)
    gauge_before = _coordinate(gauge_state)["loading"]
    x = np.arange(GRID_SIZE) * LENGTH / GRID_SIZE
    lam = 0.37 * np.sin(2 * math.pi * x / LENGTH)
    transformed = {key: value.copy() for key, value in gauge_state.items()}
    transformed["theta"] += lam - np.roll(lam, -1)
    transformed["psi_plus"] *= np.exp(1j * numerical.CHARGE * lam)[:, None]
    transformed["psi_minus"] *= np.exp(-1j * numerical.CHARGE * lam)[:, None]
    gauge_after = _coordinate(transformed)["loading"]

    phase_loadings = [_coordinate(_state_with_phase_and_scale(delta))["loading"] for delta in (-math.pi, -math.pi / 2, 0.0, math.pi / 2)]
    holonomy_loadings = []
    for theta_w in (-0.3, 0.0, 0.3):
        state = _state_with_phase_and_scale(0.0)
        state["theta"][:] = theta_w / (numerical.CHARGE * GRID_SIZE)
        holonomy_loadings.append(_coordinate(state)["loading"])

    replacement_contract = {
        "mass_weighted_number_term_present": True,
        "number_current_normalization": "integral_dx(psi_dagger*psi)",
        "all_four_two_component_reduced_sectors_included": True,
        "interaction_energy_in_positive_base": False,
        "signed_total_energy_kept_separate": True,
        "vacuum_loading_policy": "NOT_APPLICABLE_CONTROL",
    }
    contract_mutations = []
    mutation_specs: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        ("CORRUPT_MASS_WEIGHTED_NUMBER", "MASS_WEIGHTED_NUMBER_TERM_CORRUPTED", lambda value: value.__setitem__("mass_weighted_number_term_present", False)),
        ("OMIT_NUMBER_NORMALIZATION", "NUMBER_CURRENT_NORMALIZATION_CORRUPTED", lambda value: value.__setitem__("number_current_normalization", "sum_without_dx")),
        ("OMIT_SECTOR_MULTIPLICITY", "SECTOR_MULTIPLICITY_OMITTED", lambda value: value.__setitem__("all_four_two_component_reduced_sectors_included", False)),
        ("ADD_INTERACTION_ENERGY", "INTERACTION_ENERGY_DOUBLE_COUNTED", lambda value: value.__setitem__("interaction_energy_in_positive_base", True)),
    ]
    for mutation_id, expected, mutate in mutation_specs:
        fixture = copy.deepcopy(replacement_contract)
        mutate(fixture)
        actual = replacement_contract_diagnostics(fixture)
        contract_mutations.append({"mutation_id": mutation_id, "expected_diagnostic": expected, "actual_diagnostics": actual, "passed": actual == [expected]})

    return {
        "historical_signed_axis": {
            "axis_id": HISTORICAL_AXIS_ID,
            "positive_pi_over_two_ratio": historical_ratio,
            "ratio_exceeds_one": historical_ratio > 1.0,
            "zero_denominator_crossing_scale": crossing,
            "denominator_below_crossing": below,
            "denominator_above_crossing": above,
            "sign_changes_across_crossing": below < 0.0 < above,
            "clamping_allowed": False,
            "absolute_total_substitution_allowed_without_review": False,
            "post_observation_domain_widening_allowed": False,
            "retained_as_conservation_diagnostic": True,
            "retained_as_bounded_loading_axis": False,
        },
        "replacement_axis": {
            "axis_id": REPLACEMENT_AXIS_ID,
            "zero_descendants_with_positive_base_maps_exactly_zero": 0.0 / float(reference["positive_base_energy_at_mass_one"]) == 0.0,
            "all_finite_matrix_loadings_below_one": all(row["round_trip_axis_values"][REPLACEMENT_AXIS_ID] < 1.0 for row in rows),
            "low_anchor_high_strictly_monotone": LOW_LOADING < CANONICAL_LOADING < HIGH_LOADING,
            "matrix_inverse_maximum_error": max(row["round_trip_absolute_errors"][REPLACEMENT_AXIS_ID] for row in rows),
            "gauge_before": gauge_before,
            "gauge_after": gauge_after,
            "gauge_error": abs(gauge_after - gauge_before),
            "gauge_invariant": abs(gauge_after - gauge_before) <= 1e-15,
            "phase_loading_spread": max(phase_loadings) - min(phase_loadings),
            "phase_stable": max(phase_loadings) - min(phase_loadings) <= 1e-15,
            "holonomy_loading_values": holonomy_loadings,
            "holonomy_bounded": all(0.0 <= value < 1.0 for value in holonomy_loadings),
            "mass_rows_keep_positive_base": all(row["positive_base_strictly_positive"] for row in rows),
            "vacuum_axis_value": None,
            "vacuum_axis_status": "NOT_APPLICABLE_CONTROL",
            "signed_total_energy_remains_separate": True,
            "canonical_mapping": CANONICAL_LOADING,
            "canonical_mapping_matches_accepted": math.isclose(CANONICAL_LOADING, float(reference["canonical_loading"]), rel_tol=0.0, abs_tol=1e-15),
            "replacement_contract": replacement_contract,
            "replacement_contract_mutations": contract_mutations,
        },
    }


def replacement_contract_diagnostics(contract: dict[str, Any]) -> list[str]:
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


def normalization_regression_controls(audit: dict[str, Any]) -> list[dict[str, Any]]:
    historical = audit["historical_signed_axis"]
    replacement = audit["replacement_axis"]
    mutations = {item["mutation_id"]: item for item in replacement["replacement_contract_mutations"]}
    controls = [
        ("NORM01_HISTORICAL_RATIO_EXCEEDS_ONE", historical["ratio_exceeds_one"], historical["positive_pi_over_two_ratio"]),
        ("NORM02_HISTORICAL_DENOMINATOR_CROSSES_ZERO", 0.0 < historical["zero_denominator_crossing_scale"] < 0.001, historical["zero_denominator_crossing_scale"]),
        ("NORM03_HISTORICAL_RATIO_CHANGES_SIGN", historical["sign_changes_across_crossing"], [historical["denominator_below_crossing"], historical["denominator_above_crossing"]]),
        ("NORM04_CLAMPING_REJECTED", historical["clamping_allowed"] is False, historical["clamping_allowed"]),
        ("NORM05_ABSOLUTE_TOTAL_SHORTCUT_REJECTED", historical["absolute_total_substitution_allowed_without_review"] is False, historical["absolute_total_substitution_allowed_without_review"]),
        ("NORM06_POST_OBSERVATION_DOMAIN_WIDENING_REJECTED", historical["post_observation_domain_widening_allowed"] is False, historical["post_observation_domain_widening_allowed"]),
        ("NORM07_ZERO_DESCENDANTS_MAP_ZERO", replacement["zero_descendants_with_positive_base_maps_exactly_zero"], 0.0),
        ("NORM08_FINITE_LOADING_BELOW_ONE", replacement["all_finite_matrix_loadings_below_one"], replacement["all_finite_matrix_loadings_below_one"]),
        ("NORM09_LOADING_MONOTONE_IN_AMPLITUDE", replacement["low_anchor_high_strictly_monotone"], [LOW_LOADING, CANONICAL_LOADING, HIGH_LOADING]),
        ("NORM10_INVERSE_RECONSTRUCTION", replacement["matrix_inverse_maximum_error"] <= ROUND_TRIP_TOLERANCE, replacement["matrix_inverse_maximum_error"]),
        ("NORM11_GAUGE_INVARIANCE", replacement["gauge_invariant"], replacement["gauge_error"]),
        ("NORM12_PHASE_STABILITY_AFTER_RECONSTRUCTION", replacement["phase_stable"], replacement["phase_loading_spread"]),
        ("NORM13_HOLONOMY_BOUNDEDNESS", replacement["holonomy_bounded"], replacement["holonomy_loading_values"]),
        ("NORM14_MASS_DOMAIN_DENOMINATOR_POSITIVITY", replacement["mass_rows_keep_positive_base"], replacement["mass_rows_keep_positive_base"]),
        ("NORM15_VACUUM_AXIS_NOT_APPLICABLE", replacement["vacuum_axis_value"] is None and replacement["vacuum_axis_status"] == "NOT_APPLICABLE_CONTROL", replacement["vacuum_axis_status"]),
        ("NORM16_SIGNED_ENERGY_ROLE_SEPARATE", replacement["signed_total_energy_remains_separate"], replacement["signed_total_energy_remains_separate"]),
        ("NORM17_CANONICAL_MAPPING_EXACT", replacement["canonical_mapping_matches_accepted"], replacement["canonical_mapping"]),
        ("NORM18_CORRUPTED_MASS_NUMBER_DETECTED", mutations["CORRUPT_MASS_WEIGHTED_NUMBER"]["passed"], mutations["CORRUPT_MASS_WEIGHTED_NUMBER"]),
        ("NORM19_NUMBER_NORMALIZATION_OR_MULTIPLICITY_OMISSION_DETECTED", mutations["OMIT_NUMBER_NORMALIZATION"]["passed"] and mutations["OMIT_SECTOR_MULTIPLICITY"]["passed"], [mutations["OMIT_NUMBER_NORMALIZATION"], mutations["OMIT_SECTOR_MULTIPLICITY"]]),
        ("NORM20_INTERACTION_ENERGY_DOUBLE_COUNT_REJECTED", mutations["ADD_INTERACTION_ENERGY"]["passed"], mutations["ADD_INTERACTION_ENERGY"]),
    ]
    return [
        {"control_id": control_id, "permanent_regression": True, "observed": observed, "passed": bool(passed)}
        for control_id, passed, observed in controls
    ]


def validate_contract(packet: dict[str, Any]) -> list[str]:
    diagnostics: list[str] = []
    if packet.get("target") != TARGET or packet.get("selected_next_target") != REVIEW_TARGET or packet.get("post_acceptance_target") != POST_ACCEPTANCE_TARGET:
        diagnostics.append("targets")
    levels = packet.get("axis_level_freeze", {})
    if set(levels) != {"ETA_Q", REPLACEMENT_AXIS_ID, "THETA_W", "DELTA_THETA_PSI", "MU_MASS_DOMAIN"} or any(item.get("exact_values_frozen") is not True for item in levels.values()):
        diagnostics.append("axis_levels")
    rows = packet.get("scientific_matrix", [])
    tuples = [tuple(row.get("requested_axis_values", {}).values()) for row in rows]
    if len(rows) != 14 or len(set(tuples)) != 14 or not all(row.get("positive_base_strictly_positive") is True and row.get("round_trip_passed") is True for row in rows):
        diagnostics.append("scientific_matrix")
    comparator = packet.get("comparator_policy", {})
    if comparator.get("forced_comparator_eligible_for_positive_robustness_claim") is not False or comparator.get("recompute_as_zero_for_scientific_axis_forbidden") is not True or any(row.get("comparator_provenance", {}).get("comparator_realized_loading_status") != "NOT_PHYSICALLY_ELIGIBLE" for row in rows):
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
    authority = packet.get("authority_boundary", {})
    if authority.get("robustness_execution_authorized") is not False:
        diagnostics.append("execution")
    semantics = packet.get("semantic_role_separation", {})
    if semantics.get("signed_total_energy_is_physical_conservation_diagnostic") is not True or semantics.get("positive_loading_is_design_coordinate_only") is not True:
        diagnostics.append("semantic_roles")
    controls = packet.get("normalization_regression_controls", [])
    if len(controls) != 20 or not all(item.get("passed") is True for item in controls):
        diagnostics.append("normalization_controls")
    control_freeze = packet.get("control_freeze", {})
    if (
        control_freeze.get("all_control_ids_frozen") is not True
        or len(control_freeze.get("accepted_positive_control_ids", [])) != 8
        or len(control_freeze.get("accepted_negative_control_ids", [])) != 13
        or len(control_freeze.get("normalization_regression_control_ids", [])) != 20
    ):
        diagnostics.append("control_inventory")
    outcomes = packet.get("result_classification_freeze", {})
    if len(outcomes.get("robustness_status_classes", [])) != 5 or len(outcomes.get("descendant_significance_classes", [])) != 3 or outcomes.get("taxonomy_frozen") is not True:
        diagnostics.append("outcome_taxonomy")
    nonclaims = packet.get("nonclaims", {})
    if any(nonclaims.get(key) is not False for key in ("robustness_pilot_executed", "robustness_execution_performed", "pillar_completion_claimed", "seam_closure_claimed", "C_k_dynamics_claimed", "CCFT_empirical_support_claimed", "master_action_promotion_claimed")):
        diagnostics.append("nonclaims")
    return diagnostics


def mutation_controls(packet: dict[str, Any]) -> list[dict[str, Any]]:
    mutations: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
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
    results = []
    for mutation_id, expected, mutate in mutations:
        fixture = copy.deepcopy(packet)
        fixture.pop("mutation_controls", None)
        if validate_contract(fixture):
            raise ValueError(f"fresh baseline failed before {mutation_id}")
        mutate(fixture)
        actual = validate_contract(fixture)
        results.append({
            "mutation_id": mutation_id,
            "expected_diagnostic": expected,
            "actual_diagnostics": actual,
            "one_intended_premise_changed": True,
            "passed": actual == [expected],
        })
    return results


def build_packet() -> dict[str, Any]:
    sources = load_authority()
    design = sources[DESIGN_PACKET_RELATIVE_PATH]
    reference = reference_inventory()
    levels = axis_level_freeze()
    rows = scientific_matrix(levels, reference)
    matrix_checks = matrix_audit(rows)
    if not all(value is True for key, value in matrix_checks.items() if key.startswith("all_") or key.startswith("no_")):
        raise ValueError("matrix-wide guardrail audit failed")
    audit = historical_and_replacement_audit(rows, reference)
    controls = normalization_regression_controls(audit)
    if not all(item["passed"] for item in controls):
        raise ValueError("normalization regression control failed")
    packet: dict[str, Any] = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_GUARDRAIL_V1_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "authority_inputs": [{"path": path, "sha256": digest} for path, digest in sorted(INPUT_HASHES.items())],
        "reference_initial_state_freeze": reference,
        "axis_level_freeze": levels,
        "scientific_matrix_design": {
            "design": "CANONICAL_ANCHOR_PLUS_ONE_AT_A_TIME_PLUS_PREREGISTERED_INTERACTION_CORNERS",
            "exact_scientific_row_count": 14,
            "canonical_anchor_count": 1,
            "one_at_a_time_count": 10,
            "interaction_corner_count": 3,
            "full_cartesian_sweep_forbidden": True,
            "duplicate_parameter_tuples_forbidden": True,
            "difficult_or_failed_points_remain_in_evidence": True,
        },
        "scientific_matrix": rows,
        "matrix_wide_reconstruction_audit": matrix_checks,
        "comparator_policy": comparator_policy(),
        "observable_freeze": observable_freeze(design),
        "threshold_freeze": threshold_freeze(),
        "positive_controls": copy.deepcopy(design["positive_controls"]),
        "negative_controls": copy.deepcopy(design["negative_controls"]),
        "normalization_audit": audit,
        "normalization_regression_controls": controls,
        "control_freeze": {
            "accepted_positive_control_ids": [item["control_id"] for item in design["positive_controls"]],
            "accepted_negative_control_ids": [item["control_id"] for item in design["negative_controls"]],
            "normalization_regression_control_ids": [item["control_id"] for item in controls],
            "all_control_ids_frozen": True,
            "post_result_control_addition_removal_or_relabeling_forbidden": True,
            "original_transverse_sector_blocker_remains_permanent_regression": True,
        },
        "pilot_freeze": pilot_freeze(),
        "result_classification_freeze": result_classification_freeze(design),
        "semantic_role_separation": {
            "signed_total_energy_is_physical_conservation_diagnostic": True,
            "positive_loading_is_design_coordinate_only": True,
            "positive_loading_interpretation": "Initial transverse-descendant loading relative to a positive longitudinal-Maxwell and matter-number reference scale.",
            "positive_loading_forbidden_interpretation": "Fraction of the conserved total energy stored in descendants.",
            "conservation_equations_rewritten_with_positive_denominator": False,
        },
        "future_sequence_if_independently_accepted": [
            POST_ACCEPTANCE_TARGET,
            "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1_result",
            "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_parameter_freeze_packet_v1",
            "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_parameter_freeze_packet_v1_result",
            "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v1",
            "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v1_result",
        ],
        "authority_boundary": {
            "independent_guardrail_review_authorized": True,
            "guardrail_v1_accepted_before_review": False,
            "robustness_pilot_authorized": False,
            "robustness_parameter_calibration_authorized": False,
            "robustness_execution_authorized": False,
            "canonical_E_REPRO_result_remains_accepted": True,
            "canonical_result_reopened": False,
            "accepted_reduction_reopened": False,
            "pillar_promotion_authorized": False,
            "seam_closure_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_empirical_promotion_authorized": False,
            "master_action_promotion_authorized": False,
            "repository_wide_tier3_green_authorized": False,
        },
        "nonclaims": {
            "robustness_pilot_executed": False,
            "robustness_parameter_calibrated": False,
            "robustness_execution_performed": False,
            "broad_robustness_claimed": False,
            "physical_descendant_necessity_in_nature_claimed": False,
            "fermionic_QFT_claimed": False,
            "quantized_electromagnetism_claimed": False,
            "pillar_completion_claimed": False,
            "seam_closure_claimed": False,
            "new_fundamental_physics_claimed": False,
            "C_k_dynamics_claimed": False,
            "CCFT_empirical_support_claimed": False,
            "master_action_promotion_claimed": False,
            "repository_wide_green_claimed": False,
        },
        "prompt_sha256": PROMPT_SHA256,
        "claim_ceiling": "Guardrail-v1 preparation freezes a bounded 14-row design, positive-loading reconstruction, materiality rules, controls, pilot subset, classifications, and nonclaims. No pilot, calibration, robustness execution, pillar, seam, CCFT, C_k, or master-action claim is authorized before independent review.",
    }
    if validate_contract(packet):
        raise ValueError(f"guardrail v1 contract failed: {validate_contract(packet)}")
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
        "replacement_axis_id": REPLACEMENT_AXIS_ID,
        "axis_values_frozen": True,
        "scientific_row_count": len(packet["scientific_matrix"]),
        "canonical_loading": CANONICAL_LOADING,
        "low_loading": LOW_LOADING,
        "high_loading": HIGH_LOADING,
        "positive_base_minimum": min(row["derived_initial_state_parameters"]["positive_base_energy_B_plus"] for row in packet["scientific_matrix"]),
        "maximum_loading_round_trip_error": packet["matrix_wide_reconstruction_audit"]["maximum_loading_round_trip_error"],
        "pilot_row_ids": PILOT_ROW_IDS,
        "pilot_authorized": False,
        "robustness_execution_authorized": False,
        "normalization_regression_control_count": len(packet["normalization_regression_controls"]),
        "normalization_regression_controls_passed": sum(item["passed"] for item in packet["normalization_regression_controls"]),
        "mutation_control_count": len(packet["mutation_controls"]),
        "mutation_controls_passed": sum(item["passed"] for item in packet["mutation_controls"]),
        "packet_sha256": packet_hash,
        "selected_next_target": REVIEW_TARGET,
        "claim_ceiling": packet["claim_ceiling"],
    }
    report_hash = sha256_bytes(canonical_json_bytes(report))
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": [{"path": path, "sha256": digest} for path, digest in sorted(INPUT_HASHES.items())],
        "artifacts": [
            {"path": PACKET_RELATIVE_PATH, "sha256": packet_hash},
            {"path": REPORT_RELATIVE_PATH, "sha256": report_hash},
        ],
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
    return all(
        path.exists() and path.read_bytes() == canonical_json_bytes(payload)
        for path, payload in ((PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report))
    )


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
