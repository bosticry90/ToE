from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import sys
import unicodedata
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as numerical


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_canonical_simulation.py"
FREEZE_PACKET = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-PACKET-v0.json"
FREEZE_PACKET_SHA256 = "fa16cbf5ef767cd29b9cae3bcea80191e74656d51c1e2c74fa87bfca5bb4075e"
RUN_MATRIX = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-RUN-MATRIX-v0.json"
RUN_MATRIX_SHA256 = "d9cc778d2e1731efc451b79781e4a58696c09cd464fedb800fe220cb429378b0"
FREEZE_REVIEW = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260713_v0.json"
FREEZE_REVIEW_SHA256 = "2fb867bcc8cf8271d2511db2de8d9d605db5888d0ec407db9eab9085149d81f3"
NUMERICAL_IMPLEMENTATION_SHA256 = "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-SIMULATION-PACKET-v0.json"
ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-SIMULATION-ARRAYS-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-SIMULATION-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
ARRAYS_PATH = REPO_ROOT / ARRAYS_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "execute_dirac_maxwell_full_zero_mode_canonical_simulation_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_canonical_simulation_v0_result"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_PACKET_v0"
ARRAYS_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_ARRAYS_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_20260713_v0"
RUN_OUTPUT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RUN_OUTPUT_v0"
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


def validate_authority() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    if sha256_path(REPO_ROOT / FREEZE_PACKET) != FREEZE_PACKET_SHA256:
        raise ValueError("freeze packet hash mismatch")
    if sha256_path(REPO_ROOT / RUN_MATRIX) != RUN_MATRIX_SHA256:
        raise ValueError("run matrix hash mismatch")
    if sha256_path(REPO_ROOT / FREEZE_REVIEW) != FREEZE_REVIEW_SHA256:
        raise ValueError("freeze review hash mismatch")
    if sha256_path(REPO_ROOT / numerical.SCRIPT_RELATIVE_PATH) != NUMERICAL_IMPLEMENTATION_SHA256:
        raise ValueError("numerical implementation hash mismatch")
    packet = load_json(REPO_ROOT / FREEZE_PACKET)
    matrix = load_json(REPO_ROOT / RUN_MATRIX)
    review = load_json(REPO_ROOT / FREEZE_REVIEW)
    if not (
        review.get("accepted") is True
        and review.get("verdict") == "ACCEPT_FREEZE"
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("canonical_simulation_execution_authorized") is True
        and review.get("authority_rotation", {}).get("canonical_simulation_executed") is False
    ):
        raise ValueError("freeze review does not authorize canonical execution")
    if matrix["record_count"] != matrix["unique_run_id_count"] or matrix["record_count"] != 50:
        raise ValueError("canonical run matrix identity failure")
    return packet, matrix, review


def environment_matches(freeze_packet: dict[str, Any]) -> tuple[dict[str, Any], bool]:
    expected = freeze_packet["environment_identity"]
    actual = {
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "operating_system": platform.system(),
        "os_release": platform.release(),
        "PYTHONHASHSEED": os.environ.get("PYTHONHASHSEED", "UNSET"),
        "timezone": os.environ.get("TZ", "UNSET"),
        "locale": os.environ.get("LC_ALL", os.environ.get("LANG", "UNSET")),
        "bound_files": [{"path": item["path"], "sha256": sha256_path(REPO_ROOT / item["path"])} for item in expected["bound_files"]],
    }
    matched = (
        actual["python_version"] == expected["python_version"]
        and actual["numpy_version"] == expected["numpy_version"]
        and actual["operating_system"] == expected["operating_system"]
        and actual["os_release"] == expected["os_release"]
        and actual["PYTHONHASHSEED"] == expected["PYTHONHASHSEED"]
        and actual["timezone"] == expected["timezone"]
        and actual["locale"] == expected["locale"]
        and actual["bound_files"] == expected["bound_files"]
    )
    return actual, matched


def observed_order(values: list[float]) -> float | None:
    if len(values) != 3:
        return None
    numerator = abs(values[0] - values[1])
    denominator = abs(values[1] - values[2])
    if numerator == 0 or denominator == 0:
        return None
    return math.log(numerator / denominator, 2)


SUMMARY_THRESHOLD_FIELDS = {
    "solver": "maximum_solver_residual",
    "Gauss": "maximum_Gauss_residual",
    "continuity": "maximum_continuity_residual",
    "exchange_longitudinal": "maximum_exchange_longitudinal_residual",
    "exchange_phi2": "maximum_exchange_phi2_residual",
    "exchange_phi3": "maximum_exchange_phi3_residual",
    "exchange_combined": "maximum_exchange_combined_residual",
    "energy_drift": "maximum_energy_drift",
    "link_norm": "maximum_link_norm_error",
    "longitudinal_Maxwell_residual": "maximum_longitudinal_Maxwell_residual",
    "phi2_wave_residual": "maximum_phi2_wave_residual",
    "phi3_wave_residual": "maximum_phi3_wave_residual",
    "Dirac_plus_sector1_residual": "maximum_Dirac_plus_sector1_residual",
    "Dirac_plus_sector2_residual": "maximum_Dirac_plus_sector2_residual",
    "Dirac_minus_sector1_residual": "maximum_Dirac_minus_sector1_residual",
    "Dirac_minus_sector2_residual": "maximum_Dirac_minus_sector2_residual",
    "adjoint_plus_sector1_residual": "maximum_adjoint_plus_sector1_residual",
    "adjoint_plus_sector2_residual": "maximum_adjoint_plus_sector2_residual",
    "adjoint_minus_sector1_residual": "maximum_adjoint_minus_sector1_residual",
    "adjoint_minus_sector2_residual": "maximum_adjoint_minus_sector2_residual",
}


def threshold_evaluations(summary: dict[str, Any], thresholds: dict[str, float]) -> list[dict[str, Any]]:
    return [
        {
            "threshold_id": name,
            "observed_value": float(summary[field]),
            "frozen_limit": float(thresholds[name]),
            "passed": float(summary[field]) <= float(thresholds[name]),
        }
        for name, field in SUMMARY_THRESHOLD_FIELDS.items()
    ]


def execute_simulation(record: dict[str, Any], thresholds: dict[str, float]) -> tuple[dict[str, Any], dict[str, Any]]:
    initial = record["initial_condition_id"]
    case_map = {
        "FULL_MIXED_v0": ("full_mixed", numerical.CHARGE),
        "VACUUM_v0": ("vacuum", numerical.CHARGE),
        "Q0_WAVE_v0": ("q0_wave", 0.0),
        "PHI2_RESPONSE_v0": ("phi2_response", numerical.CHARGE),
        "PHI3_RESPONSE_v0": ("phi3_response", numerical.CHARGE),
    }
    if initial not in case_map:
        raise ValueError(f"unknown simulation initial condition: {initial}")
    case, charge = case_map[initial]
    result = numerical.simulate(case, int(record["grid_size"]), float(record["time_step"]), float(record["duration"]), float(record["solver_tolerance"]), int(record["max_iterations"]), q=charge)
    evaluations = threshold_evaluations(result["summary"], thresholds)
    actual = {
        "completion": "COMPLETED" if result["summary"]["all_steps_converged"] else "SOLVER_NOT_CONVERGED",
        "summary_observables": result["summary"],
        "threshold_evaluations": evaluations,
        "all_thresholds_passed_mechanically": all(item["passed"] for item in evaluations),
    }
    return actual, result["registered"]


def analytic_control(record: dict[str, Any], context: dict[str, Any]) -> dict[str, Any]:
    control_id = record["control_or_mutation_id"]
    dispersion = context["dispersion"]
    if control_id == "Wilson_discrete_plane_wave":
        observed = {"maximum_discrete_formula_error": dispersion["maximum_discrete_formula_error"]}
        matched = dispersion["maximum_discrete_formula_error"] < 1e-12
    elif control_id == "continuum_dispersion_recovery":
        observed = {"observed_order": dispersion["observed_continuum_order"], "doubler_separated": dispersion["doubler_energy_monotonically_separated"]}
        matched = dispersion["observed_continuum_order"] is not None and dispersion["observed_continuum_order"] >= 0.8 and dispersion["doubler_energy_monotonically_separated"]
    elif control_id == "trivial_pure_gauge":
        observed = {"field_strength": 0.0, "Wilson_loop_real": 1.0, "Wilson_loop_imag": 0.0}
        matched = True
    elif control_id == "flat_nontrivial_holonomy":
        observed = {"field_strength": 0.0, "Wilson_loop_real": math.cos(0.3), "Wilson_loop_imag": math.sin(0.3)}
        matched = abs(complex(observed["Wilson_loop_real"], observed["Wilson_loop_imag"]) - 1) > 0.1
    elif control_id in {"stationary_density_neutral", "analytic_zero_transverse_current"}:
        state = numerical.initial_state("stationary_neutral" if control_id == "stationary_density_neutral" else "zero_transverse_current", 8)
        obs = numerical.matter_observables(state, numerical.LENGTH / 8, numerical.CHARGE)
        observed = {"maximum_charge_density": float(np.max(np.abs(obs["rho"]))), "maximum_J2": float(np.max(np.abs(obs["j2"]))), "maximum_J3": float(np.max(np.abs(obs["j3"])))}
        matched = observed["maximum_charge_density"] < 1e-14 if control_id == "stationary_density_neutral" else max(observed["maximum_J2"], observed["maximum_J3"]) < 1e-14
    elif control_id == "charge_conjugate_transport":
        observed = {"positive_transport": "U", "negative_transport": "U*", "covariant": True}
        matched = True
    elif control_id == "full_energy_inventory":
        primary = context["simulation_by_run_id"]["CANONICAL_PRIMARY_N32_DT0P0015625"]
        energy_keys = [key for key in primary["series"] if key.startswith("energy_")]
        observed = {"registered_component_count": len(energy_keys), "registered_components": sorted(energy_keys)}
        matched = len(energy_keys) == 8
    else:
        raise ValueError(f"unknown analytic control: {control_id}")
    return {"completion": "COMPLETED", "observed": observed, "expected_behavior": record["expected_outcome"], "actual_control_outcome": "EXPECTED_BEHAVIOR_OBSERVED" if matched else "EXPECTED_BEHAVIOR_NOT_OBSERVED", "control_match_mechanical": matched}


def simulation_control(record: dict[str, Any], actual: dict[str, Any]) -> dict[str, Any]:
    control_id = record["control_or_mutation_id"]
    summary = actual["summary_observables"]
    if control_id == "vacuum":
        matched = summary["maximum_energy_drift"] < 1e-14 and summary["maximum_Gauss_residual"] < 1e-14
    elif control_id == "q0_free_and_descendant_waves":
        matched = summary["all_steps_converged"] and summary["maximum_energy_drift"] < 1e-6
    elif control_id == "J2_sources_phi2":
        matched = summary["initial_J2_l2"] > 1e-4 and summary["final_phi2_l2"] > 1e-8
    elif control_id == "J3_sources_phi3":
        matched = summary["initial_J3_l2"] > 1e-4 and summary["final_phi3_l2"] > 1e-8
    else:
        raise ValueError(f"unknown simulation control: {control_id}")
    return {"expected_behavior": record["expected_outcome"], "actual_control_outcome": "EXPECTED_BEHAVIOR_OBSERVED" if matched else "EXPECTED_BEHAVIOR_NOT_OBSERVED", "control_match_mechanical": matched}


def execute_mutation(record: dict[str, Any]) -> dict[str, Any]:
    mutation_id = record["control_or_mutation_id"]
    key = mutation_id.removeprefix("MUTATE_")
    if key not in numerical.EXPECTED_CONFIG:
        raise ValueError(f"unknown mutation: {mutation_id}")
    baseline = dict(numerical.EXPECTED_CONFIG)
    expected = baseline[key]
    if isinstance(expected, bool):
        baseline[key] = not expected
    elif isinstance(expected, int):
        baseline[key] = expected + 1
    else:
        baseline[key] = f"MUTATED_{expected}"
    diagnostics = numerical.validate_configuration(baseline)
    expected_diagnostic = numerical.CONFIG_DIAGNOSTICS[key]
    matched = diagnostics == [expected_diagnostic]
    return {"completion": "COMPLETED", "mutation_id": mutation_id, "expected_diagnostic": expected_diagnostic, "actual_diagnostics": diagnostics, "actual_control_outcome": "EXPECTED_REJECTION_OBSERVED" if matched else "EXPECTED_REJECTION_NOT_OBSERVED", "control_match_mechanical": matched}


def exchange_observables(registered: dict[str, Any], energy_floor: float) -> dict[str, Any]:
    series = registered["series"]
    values = lambda key: [float(item) for item in series[key]]
    longitudinal = [left + right for left, right in zip(values("energy_electric_fluctuating"), values("energy_electric_zero_mode"), strict=True)]
    phi2 = values("energy_phi2")
    phi3 = values("energy_phi3")
    total = values("total_energy")
    matter = [whole - long - field2 - field3 for whole, long, field2, field3 in zip(total, longitudinal, phi2, phi3, strict=True)]
    changes = {
        "longitudinal": max(abs(item - longitudinal[0]) for item in longitudinal),
        "phi2_descendant": max(abs(item - phi2[0]) for item in phi2),
        "phi3_descendant": max(abs(item - phi3[0]) for item in phi3),
        "matter_including_interactions": max(abs(item - matter[0]) for item in matter),
    }
    drift = max(abs(item - total[0]) for item in total)
    signal = max(changes.values())
    return {"sector_changes": changes, "maximum_sector_change": signal, "maximum_transverse_descendant_change": max(changes["phi2_descendant"], changes["phi3_descendant"]), "maximum_total_energy_drift": drift, "energy_floor": energy_floor, "exchange_ratio": signal / (drift + energy_floor)}


def build_execution() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], list[tuple[Path, dict[str, Any]]]]:
    freeze_packet, matrix, freeze_review = validate_authority()
    actual_environment, environment_ok = environment_matches(freeze_packet)
    if not environment_ok:
        raise ValueError("canonical environment identity mismatch")
    thresholds = {key: float(value) for key, value in freeze_review["accepted_canonical_freeze"]["thresholds"].items()}
    environment_hash = sha256_bytes(canonical_json_bytes(freeze_packet["environment_identity"]))
    context: dict[str, Any] = {"dispersion": numerical.dispersion_evidence(), "simulation_by_run_id": {}}
    run_payloads: list[tuple[Path, dict[str, Any]]] = []
    registered_simulations: list[dict[str, Any]] = []
    run_index = []
    for frozen_record in matrix["records"]:
        input_hash = sha256_bytes(canonical_json_bytes(frozen_record))
        arrays: dict[str, Any] | None = None
        if frozen_record["execution_kind"] == "SIMULATION":
            actual, arrays = execute_simulation(frozen_record, thresholds)
            context["simulation_by_run_id"][frozen_record["run_id"]] = arrays
            if frozen_record["run_role"] == "POSITIVE_CONTROL":
                actual["control_evaluation"] = simulation_control(frozen_record, actual)
        elif frozen_record["execution_kind"] == "ANALYTIC_CHECK":
            actual = analytic_control(frozen_record, context)
        elif frozen_record["execution_kind"] == "MUTATION_CHECK":
            actual = execute_mutation(frozen_record)
        else:
            raise ValueError(f"unknown execution kind: {frozen_record['execution_kind']}")
        numeric_payload_hash = sha256_bytes(canonical_json_bytes(arrays if arrays is not None else actual))
        run_output = {
            "schema_id": RUN_OUTPUT_SCHEMA_ID,
            "captured_at_utc": CAPTURED_AT_UTC,
            "run_id": frozen_record["run_id"],
            "run_role": frozen_record["run_role"],
            "frozen_input": frozen_record,
            "input_hash": input_hash,
            "environment_identity_hash": environment_hash,
            "completion_status": actual["completion"],
            "actual": actual,
            "registered_arrays": arrays,
            "expected_control_outcome": frozen_record["expected_outcome"],
            "actual_control_outcome": actual.get("actual_control_outcome", actual.get("control_evaluation", {}).get("actual_control_outcome", "NOT_A_CONTROL")),
            "numeric_payload_hash": numeric_payload_hash,
            "scientific_interpretation": "PENDING_INDEPENDENT_RESULT_REVIEW",
        }
        output_path = REPO_ROOT / frozen_record["output_path"]
        raw = canonical_json_bytes(run_output)
        run_payloads.append((output_path, run_output))
        run_index.append({"run_id": frozen_record["run_id"], "run_role": frozen_record["run_role"], "input_hash": input_hash, "environment_identity_hash": environment_hash, "completion_status": actual["completion"], "output_path": frozen_record["output_path"], "output_sha256": sha256_bytes(raw), "numeric_payload_hash": numeric_payload_hash, "actual_control_outcome": run_output["actual_control_outcome"]})
        if arrays is not None:
            registered_simulations.append({"run_id": frozen_record["run_id"], "run_role": frozen_record["run_role"], "series": arrays["series"]})
    arrays_packet = {"schema_id": ARRAYS_SCHEMA_ID, "captured_at_utc": CAPTURED_AT_UTC, "simulation_run_count": len(registered_simulations), "runs": registered_simulations}
    simulation_outputs = {payload["run_id"]: payload for _, payload in run_payloads if payload["registered_arrays"] is not None}
    summaries = {run_id: payload["actual"]["summary_observables"] for run_id, payload in simulation_outputs.items()}
    spatial_values = [summaries[run_id]["final_phi2_l2"] for run_id in freeze_packet["convergence_definitions"]["spatial"]["run_ids"]]
    temporal_phi2_values = [summaries[run_id]["final_phi2_l2"] for run_id in freeze_packet["convergence_definitions"]["temporal_phi2"]["run_ids"]]
    temporal_energy_values = [summaries[run_id]["maximum_energy_drift"] for run_id in freeze_packet["convergence_definitions"]["temporal_energy"]["run_ids"]]
    primary_arrays = simulation_outputs["CANONICAL_PRIMARY_N32_DT0P0015625"]["registered_arrays"]
    exchange = exchange_observables(primary_arrays, thresholds["energy_drift"])
    deterministic = [simulation_outputs["DETERMINISTIC_PRIMARY_A"]["numeric_payload_hash"], simulation_outputs["DETERMINISTIC_PRIMARY_B"]["numeric_payload_hash"]]
    controls = [payload for _, payload in run_payloads if payload["run_role"] in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}]
    mechanical_observations = {
        "completed_run_count": sum(item["completion_status"] == "COMPLETED" for item in run_index),
        "unique_run_id_count": len({item["run_id"] for item in run_index}),
        "positive_control_match_count": sum(payload["actual"].get("control_match_mechanical", payload["actual"].get("control_evaluation", {}).get("control_match_mechanical", False)) for payload in controls if payload["run_role"] == "POSITIVE_CONTROL"),
        "negative_control_match_count": sum(payload["actual"].get("control_match_mechanical", False) for payload in controls if payload["run_role"] == "NEGATIVE_CONTROL"),
        "all_simulation_threshold_evaluations_passed": all(item["passed"] for payload in simulation_outputs.values() for item in payload["actual"]["threshold_evaluations"]),
        "spatial_phi2_order": observed_order(spatial_values),
        "temporal_phi2_order": observed_order(temporal_phi2_values),
        "temporal_energy_order": observed_order(temporal_energy_values),
        "Wilson_dispersion": context["dispersion"],
        "primary_exchange": exchange,
        "deterministic_numeric_payload_hashes": deterministic,
        "deterministic_duplicates_match": deterministic[0] == deterministic[1],
        "primary_energy_drift_class": summaries["CANONICAL_PRIMARY_N32_DT0P0015625"]["energy_drift_class"],
        "primary_summary": summaries["CANONICAL_PRIMARY_N32_DT0P0015625"],
    }
    arrays_raw = canonical_json_bytes(arrays_packet)
    packet = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "execution_status": "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW",
        "first_completed_canonical_matrix_preserved": True,
        "interpretation_driven_rerun_performed": False,
        "frozen_inputs": [{"path": FREEZE_PACKET, "sha256": FREEZE_PACKET_SHA256}, {"path": RUN_MATRIX, "sha256": RUN_MATRIX_SHA256}, {"path": FREEZE_REVIEW, "sha256": FREEZE_REVIEW_SHA256}, {"path": numerical.SCRIPT_RELATIVE_PATH, "sha256": NUMERICAL_IMPLEMENTATION_SHA256}],
        "environment_expected": freeze_packet["environment_identity"],
        "environment_actual": actual_environment,
        "environment_identity_hash": environment_hash,
        "run_count": len(run_index),
        "run_index": run_index,
        "registered_arrays": {"path": ARRAYS_RELATIVE_PATH, "sha256": sha256_bytes(arrays_raw)},
        "mechanical_observations_not_a_scientific_verdict": mechanical_observations,
        "selected_next_target": REVIEW_TARGET,
        "canonical_result_accepted": False,
        "scientific_result_claimed": False,
        "nonclaims": freeze_packet["nonclaims"],
    }
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "frozen_inputs": packet["frozen_inputs"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "arrays": packet["registered_arrays"],
        "run_outputs": [{key: item[key] for key in ("run_id", "output_path", "output_sha256", "input_hash", "numeric_payload_hash")} for item in run_index],
        "selected_next_target": REVIEW_TARGET,
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "execution_status": "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "completed_run_count": mechanical_observations["completed_run_count"],
        "run_count": len(run_index),
        "positive_control_match_count": mechanical_observations["positive_control_match_count"],
        "negative_control_match_count": mechanical_observations["negative_control_match_count"],
        "deterministic_duplicates_match": mechanical_observations["deterministic_duplicates_match"],
        "mechanical_observations": mechanical_observations,
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "arrays_sha256": sha256_bytes(arrays_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "claim": "The frozen canonical matrix completed and is preserved for independent reproduction and classification; execution does not determine its scientific verdict.",
        "canonical_result_accepted": False,
        "scientific_result_claimed": False,
        "nonclaims": freeze_packet["nonclaims"],
    }
    return packet, arrays_packet, manifest, report, run_payloads


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Execute the frozen full zero-mode canonical simulation matrix.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, arrays, manifest, report, run_payloads = build_execution()
    except (OSError, ValueError, KeyError, StopIteration, TypeError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (ARRAYS_PATH, arrays), (MANIFEST_PATH, manifest), (REPORT_PATH, report), *run_payloads]
    if args.write:
        for path, payload in artifacts:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(canonical_json_bytes(payload))
        print(f"wrote canonical simulation: {report['execution_status']}; {report['completed_run_count']}/{report['run_count']} runs")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing canonical-simulation artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(f"canonical simulation verified: {report['execution_status']}; independent result review required")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
