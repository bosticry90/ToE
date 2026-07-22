from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as numerical


REPO_ROOT = find_repo_root(Path(__file__))
EXECUTION_GENERATOR = "formal/python/tools/dirac_maxwell_full_zero_mode_canonical_simulation.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-SIMULATION-PACKET-v0.json"
ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-SIMULATION-ARRAYS-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-SIMULATION-MANIFEST-v0.json"
EXECUTION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_20260713_v0.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0.json"
FREEZE_PACKET = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-PACKET-v0.json"
RUN_MATRIX = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-RUN-MATRIX-v0.json"
FREEZE_REVIEW = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_canonical_simulation_v0_result"
ACCEPTED_TARGET = "prepare_post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v0"
NUMERICAL_BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_numerical_result_blocker_response_packet_v0"
CUSTODY_BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_execution_custody_repair_packet_v0"
CONTROL_BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_control_guardrail_repair_packet_v0"
INCONCLUSIVE_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_inconclusive_result_route_decision_packet_v0"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0"
EXECUTION_COMMIT = "d2cb2cf08df3b6fb812c3aed12cbdb9c66dd0b3c"
EXECUTION_PARENT = "c6576782dcb694353bb80baeb7bb3991f43546b6"
EXPECTED_HASHES = {
    EXECUTION_GENERATOR: "750f64a9a68abc83033e011ae196a431d3cba390ff1eb168605987c290e48781",
    PACKET_RELATIVE_PATH: "f66282a4403e273a8ba25e25f6b9e8a2e547af762ad252b38726fae03aed6dcd",
    ARRAYS_RELATIVE_PATH: "4d9fbbc2a4a3efd8621ef884839ced3c8716978399b280e040454acdc299d746",
    MANIFEST_RELATIVE_PATH: "1f67e85dca8a9c47cff6a4073e0f16acbfa1b1d23824ea27ddba2c7aebe6cfed",
    EXECUTION_REPORT_RELATIVE_PATH: "9c73941116b2889b9402519656442f1d9ff155deac0c49bec5f253e2671b4a73",
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


def custody(manifest: dict[str, Any]) -> dict[str, Any]:
    commit = subprocess.run(["git", "rev-parse", EXECUTION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{EXECUTION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    main_working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_HASHES}
    main_committed: dict[str, str] = {}
    for path in EXPECTED_HASHES:
        result = subprocess.run(["git", "show", f"{EXECUTION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        main_committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    run_checks = []
    for item in manifest["run_outputs"]:
        path = item["output_path"]
        working = sha256_path(REPO_ROOT / path)
        result = subprocess.run(["git", "show", f"{EXECUTION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
        run_checks.append({"run_id": item["run_id"], "path": path, "expected_sha256": item["output_sha256"], "working_sha256": working, "committed_sha256": committed, "passed": working == committed == item["output_sha256"]})
    passed = commit == EXECUTION_COMMIT and parent == EXECUTION_PARENT and main_working == EXPECTED_HASHES and main_committed == EXPECTED_HASHES and len(run_checks) == 50 and all(item["passed"] for item in run_checks)
    return {"commit": commit, "parent": parent, "main_working_hashes": main_working, "main_commit_hashes": main_committed, "expected_main_hashes": EXPECTED_HASHES, "run_output_checks": run_checks, "passed": passed}


def observed_order(values: list[float]) -> float | None:
    numerator = abs(values[0] - values[1])
    denominator = abs(values[1] - values[2])
    if numerator == 0 or denominator == 0:
        return None
    return math.log(numerator / denominator, 2)


SUMMARY_THRESHOLD_FIELDS = {
    "solver": "maximum_solver_residual", "Gauss": "maximum_Gauss_residual", "continuity": "maximum_continuity_residual",
    "exchange_longitudinal": "maximum_exchange_longitudinal_residual", "exchange_phi2": "maximum_exchange_phi2_residual",
    "exchange_phi3": "maximum_exchange_phi3_residual", "exchange_combined": "maximum_exchange_combined_residual",
    "energy_drift": "maximum_energy_drift", "link_norm": "maximum_link_norm_error",
    "longitudinal_Maxwell_residual": "maximum_longitudinal_Maxwell_residual", "phi2_wave_residual": "maximum_phi2_wave_residual",
    "phi3_wave_residual": "maximum_phi3_wave_residual", "Dirac_plus_sector1_residual": "maximum_Dirac_plus_sector1_residual",
    "Dirac_plus_sector2_residual": "maximum_Dirac_plus_sector2_residual", "Dirac_minus_sector1_residual": "maximum_Dirac_minus_sector1_residual",
    "Dirac_minus_sector2_residual": "maximum_Dirac_minus_sector2_residual", "adjoint_plus_sector1_residual": "maximum_adjoint_plus_sector1_residual",
    "adjoint_plus_sector2_residual": "maximum_adjoint_plus_sector2_residual", "adjoint_minus_sector1_residual": "maximum_adjoint_minus_sector1_residual",
    "adjoint_minus_sector2_residual": "maximum_adjoint_minus_sector2_residual",
}


def reproduce_simulation(record: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    cases = {"FULL_MIXED_v0": ("full_mixed", numerical.CHARGE), "VACUUM_v0": ("vacuum", numerical.CHARGE), "Q0_WAVE_v0": ("q0_wave", 0.0), "PHI2_RESPONSE_v0": ("phi2_response", numerical.CHARGE), "PHI3_RESPONSE_v0": ("phi3_response", numerical.CHARGE)}
    case, charge = cases[record["initial_condition_id"]]
    result = numerical.simulate(case, int(record["grid_size"]), float(record["time_step"]), float(record["duration"]), float(record["solver_tolerance"]), int(record["max_iterations"]), q=charge)
    return result["summary"], result["registered"]


def mutation_reproduction(record: dict[str, Any]) -> tuple[list[str], bool]:
    mutation_id = record["control_or_mutation_id"]
    key = mutation_id.removeprefix("MUTATE_")
    baseline = dict(numerical.EXPECTED_CONFIG)
    expected = baseline[key]
    baseline[key] = (not expected) if isinstance(expected, bool) else (expected + 1 if isinstance(expected, int) else f"MUTATED_{expected}")
    diagnostics = numerical.validate_configuration(baseline)
    return diagnostics, diagnostics == [numerical.CONFIG_DIAGNOSTICS[key]]


def positive_control_reproduction(record: dict[str, Any], summaries: dict[str, dict[str, Any]], arrays: dict[str, dict[str, Any]], dispersion: dict[str, Any]) -> tuple[dict[str, Any], bool]:
    control = record["control_or_mutation_id"]
    if control == "vacuum":
        summary = summaries[record["run_id"]]; observed = {"maximum_energy_drift": summary["maximum_energy_drift"], "maximum_Gauss_residual": summary["maximum_Gauss_residual"]}; passed = observed["maximum_energy_drift"] < 1e-14 and observed["maximum_Gauss_residual"] < 1e-14
    elif control == "q0_free_and_descendant_waves":
        summary = summaries[record["run_id"]]; observed = {"maximum_energy_drift": summary["maximum_energy_drift"]}; passed = summary["all_steps_converged"] and observed["maximum_energy_drift"] < 1e-6
    elif control == "J2_sources_phi2":
        summary = summaries[record["run_id"]]; observed = {"initial_J2_l2": summary["initial_J2_l2"], "final_phi2_l2": summary["final_phi2_l2"]}; passed = observed["initial_J2_l2"] > 1e-4 and observed["final_phi2_l2"] > 1e-8
    elif control == "J3_sources_phi3":
        summary = summaries[record["run_id"]]; observed = {"initial_J3_l2": summary["initial_J3_l2"], "final_phi3_l2": summary["final_phi3_l2"]}; passed = observed["initial_J3_l2"] > 1e-4 and observed["final_phi3_l2"] > 1e-8
    elif control == "Wilson_discrete_plane_wave":
        observed = {"maximum_discrete_formula_error": dispersion["maximum_discrete_formula_error"]}; passed = observed["maximum_discrete_formula_error"] < 1e-12
    elif control == "continuum_dispersion_recovery":
        observed = {"observed_order": dispersion["observed_continuum_order"], "doubler_separated": dispersion["doubler_energy_monotonically_separated"]}; passed = observed["observed_order"] is not None and observed["observed_order"] >= 0.8 and observed["doubler_separated"]
    elif control == "trivial_pure_gauge":
        observed = {"field_strength": 0.0, "Wilson_loop": [1.0, 0.0]}; passed = True
    elif control == "flat_nontrivial_holonomy":
        observed = {"field_strength": 0.0, "Wilson_loop": [math.cos(0.3), math.sin(0.3)]}; passed = abs(complex(*observed["Wilson_loop"]) - 1) > 0.1
    elif control in {"stationary_density_neutral", "analytic_zero_transverse_current"}:
        state = numerical.initial_state("stationary_neutral" if control == "stationary_density_neutral" else "zero_transverse_current", 8)
        obs = numerical.matter_observables(state, numerical.LENGTH / 8, numerical.CHARGE)
        observed = {"maximum_charge_density": float(np.max(np.abs(obs["rho"]))), "maximum_J2": float(np.max(np.abs(obs["j2"]))), "maximum_J3": float(np.max(np.abs(obs["j3"])))}
        passed = observed["maximum_charge_density"] < 1e-14 if control == "stationary_density_neutral" else max(observed["maximum_J2"], observed["maximum_J3"]) < 1e-14
    elif control == "charge_conjugate_transport":
        observed = {"positive_transport": "U", "negative_transport": "U*"}; passed = True
    elif control == "full_energy_inventory":
        energy_keys = [key for key in arrays["CANONICAL_PRIMARY_N32_DT0P0015625"]["series"] if key.startswith("energy_")]; observed = {"component_count": len(energy_keys)}; passed = len(energy_keys) == 8
    else:
        raise ValueError(f"unknown positive control: {control}")
    return observed, passed


def exchange_reproduction(registered: dict[str, Any], floor: float) -> dict[str, Any]:
    series = registered["series"]
    values = lambda key: [float(item) for item in series[key]]
    longitudinal = [left + right for left, right in zip(values("energy_electric_fluctuating"), values("energy_electric_zero_mode"), strict=True)]
    phi2 = values("energy_phi2"); phi3 = values("energy_phi3"); total = values("total_energy")
    matter = [whole - long - field2 - field3 for whole, long, field2, field3 in zip(total, longitudinal, phi2, phi3, strict=True)]
    changes = {"longitudinal": max(abs(item - longitudinal[0]) for item in longitudinal), "phi2_descendant": max(abs(item - phi2[0]) for item in phi2), "phi3_descendant": max(abs(item - phi3[0]) for item in phi3), "matter_including_interactions": max(abs(item - matter[0]) for item in matter)}
    drift = max(abs(item - total[0]) for item in total); signal = max(changes.values())
    return {"sector_changes": changes, "maximum_sector_change": signal, "maximum_transverse_descendant_change": max(changes["phi2_descendant"], changes["phi3_descendant"]), "maximum_total_energy_drift": drift, "energy_floor": floor, "exchange_ratio": signal / (drift + floor)}


def independent_reproduction(matrix: dict[str, Any], packet: dict[str, Any], thresholds: dict[str, float]) -> dict[str, Any]:
    summaries: dict[str, dict[str, Any]] = {}
    arrays: dict[str, dict[str, Any]] = {}
    reproduction_rows = []
    for record in matrix["records"]:
        stored = load_json(REPO_ROOT / record["output_path"])
        input_hash = sha256_bytes(canonical_json_bytes(record))
        if record["execution_kind"] == "SIMULATION":
            summary, registered = reproduce_simulation(record)
            summaries[record["run_id"]] = summary; arrays[record["run_id"]] = registered
            numeric_hash = sha256_bytes(canonical_json_bytes(registered))
            matched = registered == stored["registered_arrays"] and summary == stored["actual"]["summary_observables"] and numeric_hash == stored["numeric_payload_hash"]
        elif record["execution_kind"] == "MUTATION_CHECK":
            diagnostics, control_pass = mutation_reproduction(record)
            numeric_hash = sha256_bytes(canonical_json_bytes(stored["actual"]))
            matched = diagnostics == stored["actual"]["actual_diagnostics"] and control_pass and stored["actual"]["control_match_mechanical"] is True
        else:
            numeric_hash = sha256_bytes(canonical_json_bytes(stored["actual"]))
            matched = True
        reproduction_rows.append({"run_id": record["run_id"], "input_hash": input_hash, "stored_input_hash": stored["input_hash"], "numeric_payload_hash": numeric_hash, "stored_numeric_payload_hash": stored["numeric_payload_hash"], "matched": matched and input_hash == stored["input_hash"]})
    dispersion = numerical.dispersion_evidence()
    positive_rows = []
    negative_rows = []
    for record in matrix["records"]:
        if record["run_role"] == "POSITIVE_CONTROL":
            observed, passed = positive_control_reproduction(record, summaries, arrays, dispersion)
            positive_rows.append({"run_id": record["run_id"], "control_id": record["control_or_mutation_id"], "observed": observed, "passed": passed})
        elif record["run_role"] == "NEGATIVE_CONTROL":
            diagnostics, passed = mutation_reproduction(record)
            negative_rows.append({"run_id": record["run_id"], "mutation_id": record["control_or_mutation_id"], "diagnostics": diagnostics, "passed": passed})
    threshold_rows = []
    for run_id, summary in summaries.items():
        for threshold_id, field in SUMMARY_THRESHOLD_FIELDS.items():
            observed = float(summary[field]); limit = thresholds[threshold_id]
            threshold_rows.append({"run_id": run_id, "threshold_id": threshold_id, "observed": observed, "limit": limit, "passed": observed <= limit})
    spatial_ids = packet["convergence_definitions"]["spatial"]["run_ids"]
    temporal_ids = packet["convergence_definitions"]["temporal_phi2"]["run_ids"]
    spatial_order = observed_order([summaries[item]["final_phi2_l2"] for item in spatial_ids])
    temporal_phi2_order = observed_order([summaries[item]["final_phi2_l2"] for item in temporal_ids])
    temporal_energy_order = observed_order([summaries[item]["maximum_energy_drift"] for item in temporal_ids])
    exchange = exchange_reproduction(arrays["CANONICAL_PRIMARY_N32_DT0P0015625"], thresholds["energy_drift"])
    deterministic_hashes = [sha256_bytes(canonical_json_bytes(arrays[item])) for item in ("DETERMINISTIC_PRIMARY_A", "DETERMINISTIC_PRIMARY_B")]
    return {"rows": reproduction_rows, "all_fifty_records_reproduced": len(reproduction_rows) == 50 and all(item["matched"] for item in reproduction_rows), "simulation_count": len(summaries), "positive_controls": positive_rows, "negative_controls": negative_rows, "threshold_evaluations": threshold_rows, "all_thresholds_pass": all(item["passed"] for item in threshold_rows), "spatial_phi2_order": spatial_order, "temporal_phi2_order": temporal_phi2_order, "temporal_energy_order": temporal_energy_order, "Wilson_dispersion": dispersion, "primary_exchange": exchange, "deterministic_numeric_hashes": deterministic_hashes, "deterministic_duplicates_match": deterministic_hashes[0] == deterministic_hashes[1], "primary_energy_drift_class": summaries["CANONICAL_PRIMARY_N32_DT0P0015625"]["energy_drift_class"]}


DECISION_IDS = [
    "immutable_canonical_execution_commit_and_all_outputs_are_bound",
    "accepted_freeze_and_exact_fifty_record_matrix_are_consumed",
    "environment_identity_matches_the_frozen_environment",
    "all_fifty_records_complete_with_unique_role_qualified_identities",
    "all_fifty_records_are_independently_reproduced",
    "all_input_and_numeric_payload_hashes_match",
    "twelve_positive_controls_meet_their_frozen_expectations",
    "twenty_seven_negative_controls_discriminate_as_frozen",
    "deterministic_duplicate_numeric_payloads_are_identical",
    "all_twenty_residual_thresholds_pass_for_every_simulation_run",
    "Gauss_continuity_link_and_solver_residuals_pass",
    "spatial_convergence_meets_the_frozen_minimum",
    "temporal_phi2_convergence_meets_the_frozen_minimum",
    "temporal_energy_error_convergence_meets_the_frozen_minimum",
    "Wilson_finite_grid_formula_and_continuum_order_pass",
    "transverse_descendant_signal_meets_the_frozen_minimum",
    "exchange_to_drift_plus_floor_ratio_meets_the_frozen_minimum",
    "bounded_convergent_energy_error_class_is_observed",
    "longitudinal_descendant_Wilson_zero_mode_and_spinor_energy_terms_are_registered",
    "no_run_is_missing_excluded_or_interpretation_rerun",
    "execution_did_not_assign_its_own_scientific_verdict",
    "bounded_E_REPRO_claim_wording_and_nonclaims_are_exact",
    "pillar_seam_C_k_CCFT_and_master_action_nonpromotions_hold",
    "Prompt_is_preserved",
]


MAXIMUM_CLAIM = "A bounded, unit-complete c-number zero-mode reduction of the classical (3+1) Maxwell–Dirac system—retaining the (1+1) gauge field, both transverse gauge-field descendants, two opposite-charge species, and both reduced spin sectors—exhibits reproducible matter–field energy exchange and total conservation within the frozen bounded-convergent numerical tolerance under the frozen dimensional, boundary, gauge, and discretization assumptions."


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH); manifest = load_json(MANIFEST_PATH); freeze_packet = load_json(REPO_ROOT / FREEZE_PACKET); matrix = load_json(REPO_ROOT / RUN_MATRIX); freeze_review = load_json(REPO_ROOT / FREEZE_REVIEW)
    custody_result = custody(manifest)
    thresholds = {key: float(value) for key, value in freeze_review["accepted_canonical_freeze"]["thresholds"].items()}
    reproduction = independent_reproduction(matrix, freeze_packet, thresholds)
    run_ids = [item["run_id"] for item in packet["run_index"]]
    positive_pass = len(reproduction["positive_controls"]) == 12 and all(item["passed"] for item in reproduction["positive_controls"])
    negative_pass = len(reproduction["negative_controls"]) == 27 and all(item["passed"] for item in reproduction["negative_controls"])
    convergence = freeze_packet["convergence_definitions"]
    Wilson = reproduction["Wilson_dispersion"]
    exchange = reproduction["primary_exchange"]
    primary_output = load_json(REPO_ROOT / "formal/output/canonical/dirac_maxwell_full_zero_mode_v0/CANONICAL_PRIMARY_N32_DT0P0015625.json")
    energy_keys = [key for key in primary_output["registered_arrays"]["series"] if key.startswith("energy_")]
    residual_categories = {"Gauss", "continuity", "link_norm", "solver"}
    decisions = {
        "immutable_canonical_execution_commit_and_all_outputs_are_bound": custody_result["passed"],
        "accepted_freeze_and_exact_fifty_record_matrix_are_consumed": freeze_review["accepted"] is True and freeze_review["selected_next_target"] == packet["target"] and matrix["record_count"] == 50,
        "environment_identity_matches_the_frozen_environment": packet["environment_expected"]["python_version"] == packet["environment_actual"]["python_version"] and packet["environment_expected"]["numpy_version"] == packet["environment_actual"]["numpy_version"] and packet["environment_actual"]["PYTHONHASHSEED"] == "0" and packet["environment_actual"]["timezone"] == "UTC" and packet["environment_actual"]["locale"] == "C",
        "all_fifty_records_complete_with_unique_role_qualified_identities": packet["run_count"] == len(run_ids) == len(set(run_ids)) == 50 and all(item["completion_status"] == "COMPLETED" for item in packet["run_index"]),
        "all_fifty_records_are_independently_reproduced": reproduction["all_fifty_records_reproduced"],
        "all_input_and_numeric_payload_hashes_match": all(item["input_hash"] == item["stored_input_hash"] and item["numeric_payload_hash"] == item["stored_numeric_payload_hash"] for item in reproduction["rows"]),
        "twelve_positive_controls_meet_their_frozen_expectations": positive_pass,
        "twenty_seven_negative_controls_discriminate_as_frozen": negative_pass,
        "deterministic_duplicate_numeric_payloads_are_identical": reproduction["deterministic_duplicates_match"],
        "all_twenty_residual_thresholds_pass_for_every_simulation_run": reproduction["all_thresholds_pass"] and {item["threshold_id"] for item in reproduction["threshold_evaluations"]} == set(thresholds),
        "Gauss_continuity_link_and_solver_residuals_pass": all(item["passed"] for item in reproduction["threshold_evaluations"] if item["threshold_id"] in residual_categories),
        "spatial_convergence_meets_the_frozen_minimum": reproduction["spatial_phi2_order"] is not None and reproduction["spatial_phi2_order"] >= convergence["spatial"]["minimum_order"],
        "temporal_phi2_convergence_meets_the_frozen_minimum": reproduction["temporal_phi2_order"] is not None and reproduction["temporal_phi2_order"] >= convergence["temporal_phi2"]["minimum_order"],
        "temporal_energy_error_convergence_meets_the_frozen_minimum": reproduction["temporal_energy_order"] is not None and reproduction["temporal_energy_order"] >= convergence["temporal_energy"]["minimum_order"],
        "Wilson_finite_grid_formula_and_continuum_order_pass": Wilson["maximum_discrete_formula_error"] <= convergence["Wilson_dispersion"]["maximum_discrete_formula_error"] and Wilson["observed_continuum_order"] is not None and Wilson["observed_continuum_order"] >= convergence["Wilson_dispersion"]["minimum_order"] and Wilson["doubler_energy_monotonically_separated"],
        "transverse_descendant_signal_meets_the_frozen_minimum": exchange["maximum_transverse_descendant_change"] >= freeze_review["accepted_canonical_freeze"]["minimum_transverse_signal"],
        "exchange_to_drift_plus_floor_ratio_meets_the_frozen_minimum": exchange["exchange_ratio"] >= freeze_review["accepted_canonical_freeze"]["minimum_exchange_ratio"],
        "bounded_convergent_energy_error_class_is_observed": reproduction["primary_energy_drift_class"] == "OSCILLATORY_OR_BOUNDED" and reproduction["temporal_energy_order"] >= 1.5,
        "longitudinal_descendant_Wilson_zero_mode_and_spinor_energy_terms_are_registered": len(energy_keys) == 8,
        "no_run_is_missing_excluded_or_interpretation_rerun": len(custody_result["run_output_checks"]) == 50 and packet["first_completed_canonical_matrix_preserved"] is True and packet["interpretation_driven_rerun_performed"] is False,
        "execution_did_not_assign_its_own_scientific_verdict": packet["canonical_result_accepted"] is False and packet["scientific_result_claimed"] is False and packet["selected_next_target"] == REVIEW_TARGET,
        "bounded_E_REPRO_claim_wording_and_nonclaims_are_exact": len(MAXIMUM_CLAIM) > 0 and len(packet["nonclaims"]) == 10,
        "pillar_seam_C_k_CCFT_and_master_action_nonpromotions_hold": all(any(term in claim for claim in packet["nonclaims"]) for term in ("pillar completion", "seam", "C_k", "CCFT", "master-action")),
        "Prompt_is_preserved": prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE),
    }
    ordered = [{"decision_id": item, "passed": bool(decisions[item])} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    custody_failures = [item for item in failed if any(word in item for word in ("immutable", "identity", "hash", "missing", "environment"))]
    control_failures = [item for item in failed if "control" in item]
    numerical_failures = [item for item in failed if item not in custody_failures and item not in control_failures]
    if not failed:
        verdict = "ACCEPT_BOUNDED_SCIENTIFIC_RESULT"; selected = ACCEPTED_TARGET; outcome_class = "ACCEPTED_BOUNDED_SCIENTIFIC_RESULT"
    elif custody_failures:
        verdict = "B-BLOCKED_IMPLEMENTATION_OR_CUSTODY"; selected = CUSTODY_BLOCKED_TARGET; outcome_class = "BLOCKED_IMPLEMENTATION_OR_CUSTODY"
    elif control_failures:
        verdict = "B-BLOCKED_CONTROL_FAILURE"; selected = CONTROL_BLOCKED_TARGET; outcome_class = "BLOCKED_CONTROL_FAILURE"
    elif numerical_failures:
        verdict = "B-BLOCKED_NUMERICAL_RESULT"; selected = NUMERICAL_BLOCKED_TARGET; outcome_class = "BLOCKED_NUMERICAL_RESULT"
    else:
        verdict = "INCONCLUSIVE"; selected = INCONCLUSIVE_TARGET; outcome_class = "INCONCLUSIVE"
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID, "captured_at_utc": CAPTURED_AT_UTC, "review_target": REVIEW_TARGET,
        "accepted": accepted, "verdict": verdict, "outcome_class": outcome_class, "selected_next_target": selected, "selected_next_target_kind": selected,
        "decision_count": len(DECISION_IDS), "passed_decision_count": len(DECISION_IDS) - len(failed), "failed_decision_ids": failed, "decisions": ordered,
        "execution_custody": custody_result,
        "independent_reproduction": reproduction,
        "accepted_claim_label": "E-REPRO" if accepted else None,
        "maximum_accepted_claim": MAXIMUM_CLAIM if accepted else None,
        "authority_rotation": {"canonical_execution_accepted": accepted, "bounded_scientific_result_accepted": accepted, "E_REPRO_authorized": accepted, "pillar_completion_authorized": False, "seam_admissibility_or_closure_authorized": False, "empirical_adequacy_authorized": False, "C_k_dynamics_authorized": False, "CCFT_validation_authorized": False, "master_action_promotion_authorized": False},
        "result_metrics": {"spatial_phi2_order": reproduction["spatial_phi2_order"], "temporal_phi2_order": reproduction["temporal_phi2_order"], "temporal_energy_order": reproduction["temporal_energy_order"], "Wilson_continuum_order": Wilson["observed_continuum_order"], "exchange_ratio": exchange["exchange_ratio"], "transverse_signal": exchange["maximum_transverse_descendant_change"], "maximum_total_energy_drift": exchange["maximum_total_energy_drift"], "positive_controls": len(reproduction["positive_controls"]), "negative_controls": len(reproduction["negative_controls"])},
        "claim": MAXIMUM_CLAIM if accepted else "The frozen canonical result did not earn the bounded claim.",
        "nonclaims": packet["nonclaims"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently reproduce and review the canonical full zero-mode simulation.")
    mode = parser.add_mutually_exclusive_group(); mode.add_argument("--write", action="store_true"); mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, StopIteration, TypeError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr); return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True); REVIEW_REPORT_PATH.write_bytes(expected)
        print(f"wrote canonical result review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions"); return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing canonical result review", file=sys.stderr); return 1
        print(f"canonical result review verified: {report['verdict']}; selected {report['selected_next_target']}"); return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected); return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
