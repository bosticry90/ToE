from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
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


REPO_ROOT = find_repo_root(Path(__file__))
PREPARATION_GENERATOR = "formal/python/tools/dirac_maxwell_full_zero_mode_canonical_parameter_freeze.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-PACKET-v0.json"
RUN_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-RUN-MATRIX-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_20260713_v0.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260713_v0.json"
PILOT_V1_PACKET = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
PILOT_V1_ARRAYS = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
PILOT_V1_REVIEW = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_V1_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
RUN_MATRIX_PATH = REPO_ROOT / RUN_MATRIX_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0_result"
ACCEPTED_TARGET = "execute_dirac_maxwell_full_zero_mode_canonical_simulation_v0"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v1"
ADDITIONAL_PILOT_TARGET = "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v2"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "40e9ca671d005bc7382df0d71089a23d8ccb26fd"
PREPARATION_PARENT = "9bd080a75467806d94431041d4c4f5b14cfe1172"
EXPECTED_HASHES = {
    PREPARATION_GENERATOR: "f069237463bcf16c4914bc43ee6f8f5a8d9c6c15da8af2ebc5bd7792beb6915d",
    PACKET_RELATIVE_PATH: "fa16cbf5ef767cd29b9cae3bcea80191e74656d51c1e2c74fa87bfca5bb4075e",
    RUN_MATRIX_RELATIVE_PATH: "d9cc778d2e1731efc451b79781e4a58696c09cd464fedb800fe220cb429378b0",
    MANIFEST_RELATIVE_PATH: "4ced6618dcdc4f22f57ad9f7726a0e72dd5c94c91ca6cd30fa73273ce6c8128f",
    PREPARATION_REPORT_RELATIVE_PATH: "028e865c9a12f0c561fc945e391bf96cd009c767ce540153dca7c565a9bde2f3",
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


def round_up_one_significant(value: float) -> float:
    if value <= 0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return math.ceil(value / scale) * scale


def round_down_one_significant(value: float) -> float:
    if value <= 0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return float(f"{math.floor(value / scale) * scale:.0e}")


def matrix_audit(matrix: dict[str, Any], pilot_packet: dict[str, Any]) -> dict[str, Any]:
    records = matrix["records"]
    run_ids = [record["run_id"] for record in records]
    roles = {role: sum(record["run_role"] == role for record in records) for role in sorted({record["run_role"] for record in records})}
    expected_roles = {"DETERMINISTIC_DUPLICATE": 2, "NEGATIVE_CONTROL": 27, "POSITIVE_CONTROL": 12, "PRIMARY_COUPLED": 1, "SOLVER_TOLERANCE_VERIFY": 2, "SPATIAL_REFINEMENT": 3, "TEMPORAL_REFINEMENT": 3}
    required_fields = {"run_id", "run_role", "execution_kind", "grid_size", "time_step", "duration", "solver_tolerance", "max_iterations", "initial_condition_id", "control_or_mutation_id", "expected_outcome", "output_path"}
    primary = next(record for record in records if record["run_role"] == "PRIMARY_COUPLED")
    deterministic = [record for record in records if record["run_role"] == "DETERMINISTIC_DUPLICATE"]
    positive_ids = {record["control_or_mutation_id"] for record in records if record["run_role"] == "POSITIVE_CONTROL"}
    negative_ids = {record["control_or_mutation_id"] for record in records if record["run_role"] == "NEGATIVE_CONTROL"}
    expected_positive = {item["control_id"] for item in pilot_packet["summary"]["positive_controls"]}
    expected_negative = {item["mutation_id"] for item in pilot_packet["summary"]["negative_controls"]}
    deterministic_parameters = [{key: record[key] for key in ("grid_size", "time_step", "duration", "solver_tolerance", "max_iterations", "initial_condition_id")} for record in deterministic]
    return {
        "record_count": len(records),
        "unique_run_id_count": len(set(run_ids)),
        "reported_counts_match": matrix["record_count"] == len(records) and matrix["unique_run_id_count"] == len(set(run_ids)) and matrix["role_counts"] == roles,
        "role_counts": roles,
        "role_counts_complete": roles == expected_roles,
        "all_required_fields_present": all(set(record) == required_fields for record in records),
        "all_output_paths_are_preregistered": all(record["output_path"] == f"formal/output/canonical/dirac_maxwell_full_zero_mode_v0/{record['run_id']}.json" for record in records),
        "primary_parameters": {key: primary[key] for key in ("grid_size", "time_step", "duration", "solver_tolerance", "max_iterations")},
        "deterministic_duplicates_match": len(deterministic_parameters) == 2 and deterministic_parameters[0] == deterministic_parameters[1],
        "positive_control_inventory_matches": positive_ids == expected_positive,
        "negative_control_inventory_matches": negative_ids == expected_negative,
        "generation_policy_is_literal": matrix["generation_policy"].startswith("literal frozen core matrix") and "no filesystem discovery" in matrix["generation_policy"],
    }


def threshold_audit(packet: dict[str, Any], pilot_review: dict[str, Any], arrays: dict[str, Any]) -> dict[str, Any]:
    thresholds = packet["threshold_provenance"]
    maximums = pilot_review["reviewed_engineering_evidence"]["maximum_residuals"]
    candidates = pilot_review["reviewed_engineering_evidence"]["candidate_thresholds_unreviewed"]
    source_ids = [record["run_record_id"] for record in arrays["runs"]]
    reconstructed = []
    for item in thresholds:
        name = item["threshold_id"]
        measured = float(maximums[name])
        recomputed = round_up_one_significant(2 * measured)
        reconstructed.append({
            "threshold_id": name,
            "measurement_matches": item["pilot_measured_value"] == measured,
            "sources_match": item["pilot_source_run_ids"] == source_ids,
            "formula_matches": item["generation_formula"] == "round_up_one_significant(2 * pilot_measured_value)",
            "recomputed_value": recomputed,
            "prepared_value": item["candidate_canonical_value"],
            "accepted_candidate_matches": item["candidate_canonical_value"] == float(candidates[name]),
            "passed": item["candidate_canonical_value"] == item["recomputed_value"] == recomputed,
        })
    return {
        "threshold_count": len(thresholds),
        "threshold_ids_complete": {item["threshold_id"] for item in thresholds} == set(maximums),
        "all_reconstructed": all(item["passed"] and item["measurement_matches"] and item["sources_match"] and item["formula_matches"] and item["accepted_candidate_matches"] for item in reconstructed),
        "reconstructed_thresholds": reconstructed,
    }


def exchange_audit(packet: dict[str, Any], arrays: dict[str, Any]) -> dict[str, Any]:
    prepared = packet["exchange_signal_separation"]
    energy_floor = next(item["candidate_canonical_value"] for item in packet["threshold_provenance"] if item["threshold_id"] == "energy_drift")
    rows = []
    for role in ("SPATIAL_N32", "TEMPORAL_DT_0P0015625"):
        record = next(item for item in arrays["runs"] if item["calibration_role"] == role)
        series = record["series"]
        values = lambda key: [float(item) for item in series[key]]
        longitudinal = [left + right for left, right in zip(values("energy_electric_fluctuating"), values("energy_electric_zero_mode"), strict=True)]
        phi2 = values("energy_phi2")
        phi3 = values("energy_phi3")
        total = values("total_energy")
        matter = [whole - long - field2 - field3 for whole, long, field2, field3 in zip(total, longitudinal, phi2, phi3, strict=True)]
        changes = [max(abs(item - values_[0]) for item in values_) for values_ in (longitudinal, phi2, phi3, matter)]
        drift = max(abs(item - total[0]) for item in total)
        rows.append({"pilot_source_run_id": record["run_record_id"], "maximum_sector_change": max(changes), "maximum_transverse_descendant_change": max(changes[1], changes[2]), "maximum_total_energy_drift": drift, "exchange_ratio": max(changes) / (drift + energy_floor)})
    minimum_ratio = min(row["exchange_ratio"] for row in rows)
    minimum_transverse = min(row["maximum_transverse_descendant_change"] for row in rows)
    ratio_gate = round_down_one_significant(minimum_ratio / 2)
    signal_gate = round_down_one_significant(minimum_transverse / 2)
    prepared_rows = prepared["pilot_rows"]
    return {
        "recomputed_rows": rows,
        "row_ids_match": [row["pilot_source_run_id"] for row in rows] == [row["pilot_source_run_id"] for row in prepared_rows],
        "minimum_pilot_ratio": minimum_ratio,
        "minimum_pilot_transverse_signal": minimum_transverse,
        "recomputed_ratio_gate": ratio_gate,
        "recomputed_transverse_signal_gate": signal_gate,
        "prepared_gates_match": prepared["canonical_minimum_exchange_ratio"] == ratio_gate and prepared["canonical_minimum_transverse_signal"] == signal_gate,
        "separation_is_material": ratio_gate >= 100 and signal_gate > 0,
    }


def environment_audit(packet: dict[str, Any]) -> dict[str, Any]:
    prepared = packet["environment_identity"]
    autocrlf = subprocess.run(["git", "config", "--get", "core.autocrlf"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip() or "UNSET"
    current_files = {item["path"]: sha256_path(REPO_ROOT / item["path"]) for item in prepared["bound_files"]}
    prepared_files = {item["path"]: item["sha256"] for item in prepared["bound_files"]}
    return {
        "python_matches": prepared["python_version"] == platform.python_version(),
        "numpy_matches": prepared["numpy_version"] == np.__version__,
        "operating_system_matches": prepared["operating_system"] == platform.system() and prepared["os_release"] == platform.release(),
        "git_line_endings_match": prepared["git_core_autocrlf"] == autocrlf,
        "bound_files_match": current_files == prepared_files,
        "determinism_policy_complete": prepared["PYTHONHASHSEED"] == "0" and prepared["timezone"] == "UTC" and prepared["locale"] == "C" and prepared["UTF8_normalization"] == "NFC",
    }


DECISION_IDS = [
    "immutable_freeze_preparation_is_bound",
    "accepted_pilot_v1_review_is_the_exact_authority",
    "all_twelve_evidence_inputs_and_v0_blocker_are_preserved",
    "primary_parameter_tuple_is_reconstructed_from_accepted_pilot_candidates",
    "fifty_run_records_are_complete_unique_and_preregistered",
    "all_seven_run_role_classes_and_control_inventories_are_complete",
    "deterministic_duplicates_have_identical_inputs_and_distinct_ids",
    "all_twenty_thresholds_are_independently_reconstructed",
    "threshold_sources_measurements_rounding_and_values_are_exact",
    "exchange_ratio_and_transverse_signal_gates_are_independently_recomputed",
    "exchange_signal_is_materially_separated_from_drift_and_floor",
    "spatial_temporal_energy_and_Wilson_fit_rules_are_complete_and_immutable",
    "no_fit_member_exclusion_or_post_result_range_change_is_allowed",
    "solver_tolerance_norm_guess_cap_and_failure_behavior_are_complete",
    "energy_class_components_normalization_flux_and_multiplicity_are_complete",
    "failure_semantics_preserve_negative_inconclusive_and_blocked_results",
    "threshold_relaxation_and_interpretation_driven_reruns_are_forbidden",
    "environment_dependency_and_line_ending_identity_are_reconstructed",
    "claim_ceiling_and_all_nonpromotion_boundaries_hold",
    "only_canonical_simulation_execution_is_authorized_after_acceptance",
    "canonical_scientific_result_remains_unearned",
    "Prompt_is_preserved",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    matrix = load_json(RUN_MATRIX_PATH)
    pilot_packet = load_json(REPO_ROOT / PILOT_V1_PACKET)
    pilot_arrays = load_json(REPO_ROOT / PILOT_V1_ARRAYS)
    pilot_review = load_json(REPO_ROOT / PILOT_V1_REVIEW)
    custody_result = custody()
    matrix_result = matrix_audit(matrix, pilot_packet)
    thresholds = threshold_audit(packet, pilot_review, pilot_arrays)
    exchange = exchange_audit(packet, pilot_arrays)
    environment = environment_audit(packet)
    proposed = packet["proposed_canonical_parameters"]
    accepted_candidates = pilot_review["reviewed_engineering_evidence"]["candidate_canonical_parameters_unreviewed"]
    convergence = packet["convergence_definitions"]
    solver = packet["solver_freeze"]
    energy = packet["energy_freeze"]
    failure = packet["failure_semantics"]
    input_map = {item["path"]: item["sha256"] for item in packet["input_artifacts"]}
    decisions = {
        "immutable_freeze_preparation_is_bound": custody_result["passed"],
        "accepted_pilot_v1_review_is_the_exact_authority": pilot_review["accepted"] is True and pilot_review["selected_next_target"] == packet["target"] == "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0",
        "all_twelve_evidence_inputs_and_v0_blocker_are_preserved": len(input_map) == 12 and packet["identity_policy"]["v0_blocker_preserved"] == "REGISTERED_RUN_IDENTITIES_NOT_UNIQUE",
        "primary_parameter_tuple_is_reconstructed_from_accepted_pilot_candidates": proposed == accepted_candidates and matrix_result["primary_parameters"] == {"grid_size": proposed["N"], "time_step": proposed["dt"], "duration": proposed["duration"], "solver_tolerance": proposed["solver_tolerance"], "max_iterations": proposed["max_iterations"]},
        "fifty_run_records_are_complete_unique_and_preregistered": matrix_result["record_count"] == matrix_result["unique_run_id_count"] == 50 and matrix_result["reported_counts_match"] and matrix_result["all_required_fields_present"] and matrix_result["all_output_paths_are_preregistered"],
        "all_seven_run_role_classes_and_control_inventories_are_complete": matrix_result["role_counts_complete"] and matrix_result["positive_control_inventory_matches"] and matrix_result["negative_control_inventory_matches"],
        "deterministic_duplicates_have_identical_inputs_and_distinct_ids": matrix_result["deterministic_duplicates_match"],
        "all_twenty_thresholds_are_independently_reconstructed": thresholds["threshold_count"] == 20 and thresholds["threshold_ids_complete"] and thresholds["all_reconstructed"],
        "threshold_sources_measurements_rounding_and_values_are_exact": all(item["measurement_matches"] and item["sources_match"] and item["formula_matches"] and item["accepted_candidate_matches"] for item in thresholds["reconstructed_thresholds"]),
        "exchange_ratio_and_transverse_signal_gates_are_independently_recomputed": exchange["row_ids_match"] and exchange["prepared_gates_match"],
        "exchange_signal_is_materially_separated_from_drift_and_floor": exchange["separation_is_material"],
        "spatial_temporal_energy_and_Wilson_fit_rules_are_complete_and_immutable": convergence["spatial"]["minimum_order"] == 0.8 and convergence["temporal_phi2"]["minimum_order"] == 1.5 and convergence["temporal_energy"]["minimum_order"] == 1.5 and convergence["Wilson_dispersion"]["grids"] == [64, 128, 256],
        "no_fit_member_exclusion_or_post_result_range_change_is_allowed": all(convergence[key]["exclusions"] == "none" for key in ("spatial", "temporal_phi2", "temporal_energy", "Wilson_dispersion")) and convergence["post_execution_fit_range_changes"] == "forbidden",
        "solver_tolerance_norm_guess_cap_and_failure_behavior_are_complete": solver["tolerance"] == proposed["solver_tolerance"] and solver["maximum_iterations"] == proposed["max_iterations"] and solver["relative_tolerance"] is False and "infinity norm" in solver["norm"] and "explicit-Euler predictor" in solver["initial_guess"] and "no retry" in solver["failure_behavior"],
        "energy_class_components_normalization_flux_and_multiplicity_are_complete": energy["classification"] == "BOUNDED_CONVERGENT_ENERGY_ERROR" and len(energy["registered_components"]) == 8 and energy["Wilson_zero_mode_and_descendant_terms_required"] is True and "periodic S1" in energy["boundary_flux"] and "four two-component" in energy["sector_multiplicity"],
        "failure_semantics_preserve_negative_inconclusive_and_blocked_results": len(failure) == 11 and "inconclusive" in failure["exchange_signal_failure"] and "B-BLOCKED" in failure["energy_order_failure"],
        "threshold_relaxation_and_interpretation_driven_reruns_are_forbidden": "forbidden" in failure["threshold_relaxation_request"] and matrix_result["generation_policy_is_literal"],
        "environment_dependency_and_line_ending_identity_are_reconstructed": all(environment.values()),
        "claim_ceiling_and_all_nonpromotion_boundaries_hold": "not a conservation or coupled-field result" in packet["claim_ceiling"] and len(packet["nonclaims"]) == 10,
        "only_canonical_simulation_execution_is_authorized_after_acceptance": packet["post_acceptance_target"] == ACCEPTED_TARGET and packet["selected_next_target"] == REVIEW_TARGET,
        "canonical_scientific_result_remains_unearned": packet["boundary"]["scientific_result_claimed"] is False and packet["boundary"]["canonical_execution_authorized"] is False,
        "Prompt_is_preserved": prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE),
    }
    ordered = [{"decision_id": item, "passed": bool(decisions[item])} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT_FREEZE" if accepted else "B-BLOCKED",
        "selected_next_target": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "selected_next_target_kind": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_matrix_audit": matrix_result,
        "independent_threshold_audit": thresholds,
        "independent_exchange_audit": exchange,
        "independent_environment_audit": environment,
        "accepted_canonical_freeze": {
            "parameters": proposed,
            "thresholds": {item["threshold_id"]: item["candidate_canonical_value"] for item in packet["threshold_provenance"]},
            "run_matrix_path": RUN_MATRIX_RELATIVE_PATH,
            "run_matrix_sha256": sha256_path(RUN_MATRIX_PATH),
            "minimum_exchange_ratio": packet["exchange_signal_separation"]["canonical_minimum_exchange_ratio"],
            "minimum_transverse_signal": packet["exchange_signal_separation"]["canonical_minimum_transverse_signal"],
            "energy_classification": energy["classification"],
        },
        "authority_rotation": {
            "canonical_parameter_freeze_accepted": accepted,
            "canonical_parameters_frozen": accepted,
            "canonical_thresholds_frozen": accepted,
            "canonical_run_matrix_frozen": accepted,
            "canonical_simulation_execution_authorized": accepted,
            "canonical_simulation_executed": False,
            "scientific_numerical_result_claimed": False,
        },
        "blocked_review_policy": {"default_target": BLOCKED_TARGET, "additional_pilot_target_only_if_review_evidence_requires_recalibration": ADDITIONAL_PILOT_TARGET, "threshold_relaxation_allowed": False},
        "claim": "The canonical experiment is preregistered and execution is authorized; no canonical simulation or scientific result exists yet." if accepted else "The canonical parameter freeze is blocked.",
        "nonclaims": packet["nonclaims"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review the full zero-mode canonical parameter freeze.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, StopIteration, TypeError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(expected)
        print(f"wrote canonical-freeze review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing canonical-freeze review", file=sys.stderr)
            return 1
        print(f"canonical-freeze review verified: {report['verdict']}; selected {report['selected_next_target']}")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
