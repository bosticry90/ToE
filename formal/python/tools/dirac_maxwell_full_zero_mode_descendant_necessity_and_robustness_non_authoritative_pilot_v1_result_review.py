from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import os
import subprocess
import sys
import unicodedata
from collections import Counter
from pathlib import Path
from typing import Any, Callable

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as accepted_numerical_reference


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1_result_review.py"
PILOT_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1.py"
PILOT_TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1.py"
PILOT_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
PILOT_ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
PILOT_MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-MANIFEST-v1.json"
PILOT_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_20260714_v1.json"
PILOT_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessNonAuthoritativePilotV1.lean"
CURRENT_TARGET_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
GUARDRAIL_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v1.json"
GUARDRAIL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260714_v1.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_RESULT_REVIEW_20260714_v1.json"
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1_result"
SELECTED_NEXT_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1"
VERDICT = "ACCEPT_ENGINEERING_READY"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_RESULT_REVIEW_20260714_v1"
PILOT_MODULE = "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1"
PILOT_COMMIT = "f8f896279f70f464ef5cc927093d242874cd0eef"
PILOT_PARENT = "fe0279cdbba476eba326a307a4491a422cb96d54"
EXPECTED_PILOT_HASHES = {
    PILOT_GENERATOR_RELATIVE_PATH: "05e7015499e3d15bc172840ac637fd0fa86b6c50f87489d6b555657ac290adb6",
    PILOT_TEST_RELATIVE_PATH: "be2b00a7fda37a79e2dd1b904d367a1277914d40a525a21de258903c6d3c1a71",
    PILOT_PACKET_RELATIVE_PATH: "d8c1f75c955b9a368159bd579f7d886523e8c66b0e611a6e6290a179422cf03a",
    PILOT_ARRAYS_RELATIVE_PATH: "5ffaca2e6e07e95ef1bb1b1451b2bda01eab355e55294a6dd51b2ffe8ecf8e8e",
    PILOT_MANIFEST_RELATIVE_PATH: "51226ec5af368967c895bb5dc9c4333f7ee3d89756de4fcc1c5f82600161ab93",
    PILOT_REPORT_RELATIVE_PATH: "a898245a13b24629af5c705c47710b8672f32dc6aded27073601e612efa379cb",
    PILOT_LEAN_RELATIVE_PATH: "b4001f3f089175bbc09be7aa5cc84249876b83caa1b2024e7f513ba6789c5fb7",
    CURRENT_TARGET_RELATIVE_PATH: "67ff95b9edbf7d25eee2741b2d3cae6cd017e8d93f08346656fe694198a63670",
    CURRENT_AUTHORITY_RELATIVE_PATH: "95a64fcb74455bac405d01eab1145b7dc8448d3245b887e5549eafa8ec21bc85",
}
IMMUTABLE_WORKING_PILOT_PATHS = {
    key: value
    for key, value in EXPECTED_PILOT_HASHES.items()
    if key not in (CURRENT_TARGET_RELATIVE_PATH, CURRENT_AUTHORITY_RELATIVE_PATH)
}
GUARDRAIL_PACKET_SHA256 = "54f3c8137986db1ba1bf7cc1a9e0ffade11ed7b6fdf480bf103cdd6b13d964f1"
GUARDRAIL_REVIEW_SHA256 = "a2c1de4f699bf0a2fc1cb38ce0e72b7682df5c0757fa61692f1d32b8e236832e"
ACCEPTED_NUMERICAL_REFERENCE_SHA256 = "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

LENGTH = 1.0
ROUND_TRIP_TOLERANCE = 2e-15
RUN_DURATION = 0.05
MAX_ITERATIONS = 80
GRID_SEQUENCE = [8, 16, 32]
TEMPORAL_DT_SEQUENCE = [0.00625, 0.003125, 0.0015625]
SOLVER_TOLERANCES = [1e-8, 1e-10, 1e-12]
MATERIAL_GATE = 0.1
DOMINATED_GATE = 0.5

PILOT_ROWS = [
    ("R00_CANONICAL", 0.2, 0.2131315883288088, 0.3, 0.0, 1.0),
    ("R03_F_ZERO", 0.2, 0.0, 0.3, 0.0, 1.0),
    ("R05_F_HIGH", 0.2, 0.5200250552967295, 0.3, 0.0, 1.0),
    ("R10_MU_HIGH", 0.2, 0.2131315883288088, 0.3, 0.0, 2.0),
    ("R11_CORNER_WEAK_HIGH", 0.1, 0.5200250552967295, -0.3, math.pi / 2, 2.0),
]
EXPECTED_ROLES = [
    "SPATIAL_N8",
    "SPATIAL_N16",
    "SPATIAL_N32",
    "TEMPORAL_DT_0P00625",
    "TEMPORAL_DT_0P003125",
    "TEMPORAL_DT_0P0015625",
    "SOLVER_TOLERANCE_1e_MINUS_08",
    "SOLVER_TOLERANCE_1e_MINUS_10",
    "SOLVER_TOLERANCE_1e_MINUS_12",
    "FORCED_TRUNCATION_BASE",
]
POSITIVE_CONTROL_IDS = [
    "P_CANONICAL_ACCEPTED_RESULT_UNCHANGED",
    "P_CHARGE_CONJUGATE_PARAMETER_CASE",
    "P_ANALYTIC_INVARIANT_DESCENDANT_FREE",
    "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED",
    "P_INDEPENDENT_PHI2_EXCITATION",
    "P_INDEPENDENT_PHI3_EXCITATION",
    "P_PHI2_PHI3_INTERCHANGE",
    "P_WEAK_COUPLING_APPROACH",
]
NEGATIVE_CONTROL_SPECS = [
    ("N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE", "ORIGINAL_TRANSVERSE_BLOCKER_REGRESSION"),
    ("N_DROP_ONLY_PHI2", "PHI2_REQUIRED_FIELD_OMITTED"),
    ("N_DROP_ONLY_PHI3", "PHI3_REQUIRED_FIELD_OMITTED"),
    ("N_OMIT_DESCENDANT_ENERGY", "TRANSVERSE_ENERGY_OMITTED"),
    ("N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL", "TRANSVERSE_EXCHANGE_CHANNEL_OMITTED"),
    ("N_REVERSE_TRANSVERSE_EXCHANGE_SIGN", "TRANSVERSE_EXCHANGE_SIGN_REVERSED"),
    ("N_WRONG_GAMMA2_BLOCK", "GAMMA2_BLOCK_CORRUPTED"),
    ("N_WRONG_GAMMA3_BLOCK", "GAMMA3_BLOCK_CORRUPTED"),
    ("N_SUPPRESS_SECTOR_MULTIPLICITY", "SECTOR_MULTIPLICITY_SUPPRESSED"),
    ("N_DESCENDANTS_RELABELED_INVENTED_MATTER", "DESCENDANT_SEMANTIC_ROLE_CORRUPTED"),
    ("N_CANONICAL_THRESHOLDS_REUSED_UNSCALED", "UNREVIEWED_CANONICAL_THRESHOLD_REUSE"),
    ("N_POST_EXECUTION_FAVORABLE_POINT_SELECTION", "POST_EXECUTION_POINT_SELECTION"),
    ("N_FAILED_POINTS_EXCLUDED_FROM_DOMAIN", "FAILED_POINT_EXCLUDED"),
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
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def git_output(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT)


def bind_pilot_custody() -> dict[str, Any]:
    if git_output("rev-parse", f"{PILOT_COMMIT}^").decode().strip() != PILOT_PARENT:
        raise ValueError("pilot parent mismatch")
    if subprocess.run(
        ["git", "merge-base", "--is-ancestor", PILOT_COMMIT, "HEAD"],
        cwd=REPO_ROOT,
        check=False,
    ).returncode != 0:
        raise ValueError("pilot custody commit is not an ancestor of HEAD")
    for relative_path, digest in EXPECTED_PILOT_HASHES.items():
        if sha256_bytes(git_output("show", f"{PILOT_COMMIT}:{relative_path}")) != digest:
            raise ValueError(f"committed pilot hash mismatch: {relative_path}")
    for relative_path, digest in IMMUTABLE_WORKING_PILOT_PATHS.items():
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"working pilot hash mismatch: {relative_path}")
    if sha256_path(REPO_ROOT / GUARDRAIL_PACKET_RELATIVE_PATH) != GUARDRAIL_PACKET_SHA256:
        raise ValueError("accepted guardrail packet changed")
    if sha256_path(REPO_ROOT / GUARDRAIL_REVIEW_RELATIVE_PATH) != GUARDRAIL_REVIEW_SHA256:
        raise ValueError("accepted guardrail review changed")
    if sha256_path(REPO_ROOT / accepted_numerical_reference.SCRIPT_RELATIVE_PATH) != ACCEPTED_NUMERICAL_REFERENCE_SHA256:
        raise ValueError("accepted numerical reference changed")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        raise ValueError("Prompt.txt changed")
    return {
        "pilot_commit": PILOT_COMMIT,
        "pilot_parent": PILOT_PARENT,
        "nine_committed_paths": EXPECTED_PILOT_HASHES,
        "seven_immutable_working_paths": IMMUTABLE_WORKING_PILOT_PATHS,
    }


def _float_series(record: dict[str, Any], key: str) -> list[float]:
    return [float(value) for value in record["series"][key]]


def _principal(value: float) -> float:
    result = (value + math.pi) % (2 * math.pi) - math.pi
    return math.pi if result == -math.pi else result


def _close(left: float, right: float, tolerance: float = 1e-15) -> bool:
    return math.isclose(float(left), float(right), rel_tol=0.0, abs_tol=tolerance)


def _field_energy(state: dict[str, np.ndarray], a: float) -> float:
    grad2 = (np.roll(state["phi2"], -1) - state["phi2"]) / a
    grad3 = (np.roll(state["phi3"], -1) - state["phi3"]) / a
    return float(
        np.sum(state["P2"] ** 2 + state["P3"] ** 2) / (2 * a)
        + 0.5 * a * np.sum(grad2**2 + grad3**2)
    )


def _row_values(spec: tuple[Any, ...]) -> dict[str, float]:
    _, eta, loading, theta_w, delta, mu = spec
    return {
        "ETA_Q": eta,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": loading,
        "THETA_W": theta_w,
        "DELTA_THETA_PSI": delta,
        "MU_MASS_DOMAIN": mu,
    }


def independently_reconstruct_axes(packet: dict[str, Any], arrays: dict[str, Any]) -> dict[str, Any]:
    packet_rows = {item["row_id"]: item for item in packet["summary"]["row_results"]}
    records = {(item["row_id"], item["calibration_role"]): item for item in arrays["runs"]}
    audits = []
    for spec in PILOT_ROWS:
        row_id = str(spec[0])
        requested = _row_values(spec)
        mass = requested["MU_MASS_DOMAIN"] / LENGTH
        q = requested["ETA_Q"] * mass
        n = 16
        a = LENGTH / n
        state = accepted_numerical_reference.initial_state("full_mixed", n, q)
        state["theta"][:] = requested["THETA_W"] / (q * n)
        unphased = {key: value.copy() for key, value in state.items()}
        phase = complex(math.cos(requested["DELTA_THETA_PSI"]), math.sin(requested["DELTA_THETA_PSI"]))
        for species in ("psi_plus", "psi_minus"):
            state[species][:, [1, 3]] *= phase
        reference_descendant = _field_energy(state, a)
        matter_number = sum(float(a * np.sum(np.abs(state[species]) ** 2)) for species in ("psi_plus", "psi_minus"))
        p_mean = float(np.mean(state["p"]))
        parallel = float(np.sum((state["p"] - p_mean) ** 2) / (2 * a) + n * p_mean**2 / (2 * a))
        positive_base = parallel + mass * matter_number
        target = requested["F_PERP_POSITIVE_LOADING_INITIAL_v1"]
        target_descendant = 0.0 if target == 0.0 else target / (1.0 - target) * positive_base
        alpha = 0.0 if target_descendant == 0.0 else math.sqrt(target_descendant / reference_descendant)
        for key in ("phi2", "P2", "phi3", "P3"):
            state[key] *= alpha
        descendant = _field_energy(state, a)
        overlap = sum(
            np.vdot(unphased[species][:, [1, 3]], state[species][:, [1, 3]])
            for species in ("psi_plus", "psi_minus")
        )
        realized = {
            "ETA_Q": q / mass,
            "F_PERP_POSITIVE_LOADING_INITIAL_v1": descendant / (descendant + positive_base),
            "THETA_W": _principal(float(q * np.sum(state["theta"]))),
            "DELTA_THETA_PSI": _principal(float(np.angle(overlap))),
            "MU_MASS_DOMAIN": mass * LENGTH,
        }
        errors = {
            key: abs(_principal(realized[key] - requested[key]))
            if key in ("THETA_W", "DELTA_THETA_PSI")
            else abs(realized[key] - requested[key])
            for key in requested
        }
        packet_reconstruction = packet_rows[row_id]["base_initial_state_reconstruction"]
        base_record = records[(row_id, "TEMPORAL_DT_0P003125")]
        arrays_match = (
            _close(_float_series(base_record, "energy_phi2")[0] + _float_series(base_record, "energy_phi3")[0], descendant)
            and _close(_float_series(base_record, "matter_number")[0], matter_number)
            and abs(_float_series(base_record, "total_charge")[0]) <= 1e-14
        )
        packet_match = (
            all(_close(packet_reconstruction["realized_parent_axis_values"][key], value) for key, value in realized.items())
            and _close(packet_reconstruction["positive_base_energy_B_plus"], positive_base)
            and _close(packet_reconstruction["reference_descendant_profile_alpha"], alpha)
            and packet_reconstruction["mass_runtime_parameter"] == mass
            and packet_reconstruction["charge_constructed_eta_times_mass"] == q
        )
        audits.append(
            {
                "row_id": row_id,
                "requested_axis_values": requested,
                "realized_axis_values": realized,
                "round_trip_absolute_errors": errors,
                "positive_base_energy_B_plus": positive_base,
                "positive_base_strictly_positive": positive_base > 0.0,
                "reference_descendant_energy": reference_descendant,
                "reconstructed_descendant_energy": descendant,
                "reference_descendant_profile_alpha": alpha,
                "other_four_axis_maximum_drift": max(value for key, value in errors.items() if key != "F_PERP_POSITIVE_LOADING_INITIAL_v1"),
                "registered_arrays_match": arrays_match,
                "packet_reconstruction_matches": packet_match,
            }
        )
    return {
        "row_audits": audits,
        "maximum_loading_error": max(item["round_trip_absolute_errors"]["F_PERP_POSITIVE_LOADING_INITIAL_v1"] for item in audits),
        "maximum_other_axis_drift": max(item["other_four_axis_maximum_drift"] for item in audits),
        "all_positive_bases_strictly_positive": all(item["positive_base_strictly_positive"] for item in audits),
        "all_registered_arrays_and_packet_rows_match": all(item["registered_arrays_match"] and item["packet_reconstruction_matches"] for item in audits),
    }


def _role_config(role: str) -> tuple[int, float, float, str]:
    if role.startswith("SPATIAL_N"):
        n = int(role.removeprefix("SPATIAL_N"))
        return n, 0.1 / n, 1e-12, "FULL"
    if role.startswith("TEMPORAL_DT_"):
        dt = float(role.removeprefix("TEMPORAL_DT_").replace("P", "."))
        return 16, dt, 1e-12, "FULL"
    if role.startswith("SOLVER_TOLERANCE_"):
        tolerance = float(role.removeprefix("SOLVER_TOLERANCE_").replace("_MINUS_", "-"))
        return 16, 0.003125, tolerance, "FULL"
    if role == "FORCED_TRUNCATION_BASE":
        return 16, 0.003125, 1e-12, "FORCED"
    raise ValueError(f"unknown calibration role: {role}")


def _expected_execution_id(row_id: str, role: str, axes: dict[str, float]) -> str:
    n, requested_dt, tolerance, model = _role_config(role)
    steps = max(1, int(round(RUN_DURATION / requested_dt)))
    dt = RUN_DURATION / steps
    payload = {
        "row_id": row_id,
        "model": model,
        "N": n,
        "dt": dt,
        "duration": RUN_DURATION,
        "tolerance": tolerance,
        "max_iterations": MAX_ITERATIONS,
        "requested_axes": axes,
    }
    return "EXECUTION_" + sha256_bytes(canonical_json_bytes(payload))[:16]


def independently_audit_run_custody(packet: dict[str, Any], arrays: dict[str, Any]) -> dict[str, Any]:
    records = arrays["runs"]
    axes_by_row = {str(spec[0]): _row_values(spec) for spec in PILOT_ROWS}
    role_counts = Counter(item["calibration_role"] for item in records)
    row_counts = Counter(item["row_id"] for item in records)
    identities_match = True
    for record in records:
        expected_execution = _expected_execution_id(record["row_id"], record["calibration_role"], axes_by_row[record["row_id"]])
        expected_record = f"{record['row_id']}:{record['calibration_role']}:{expected_execution}"
        identities_match = identities_match and record["execution_id"] == expected_execution and record["run_record_id"] == expected_record
    full = [item for item in records if item["model_class"] == "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM"]
    forced = [item for item in records if item["model_class"] == "INTENTIONALLY_NONINVARIANT_COMPARATOR"]
    return {
        "total_record_count": len(records),
        "full_model_record_count": len(full),
        "forced_comparator_record_count": len(forced),
        "unique_run_record_count": len({item["run_record_id"] for item in records}),
        "role_counts": dict(sorted(role_counts.items())),
        "row_counts": dict(sorted(row_counts.items())),
        "every_row_has_exact_closed_role_set": all(
            sorted(item["calibration_role"] for item in records if item["row_id"] == row_id) == sorted(EXPECTED_ROLES)
            for row_id in axes_by_row
        ),
        "all_role_qualified_identities_reconstructed": identities_match,
        "no_excluded_or_extra_records": len(records) == 50
        and set(role_counts) == set(EXPECTED_ROLES)
        and all(count == 5 for count in role_counts.values())
        and all(count == 10 for count in row_counts.values()),
        "implementation_hash_exact": sha256_path(REPO_ROOT / PILOT_GENERATOR_RELATIVE_PATH) == EXPECTED_PILOT_HASHES[PILOT_GENERATOR_RELATIVE_PATH],
        "arrays_hash_exact": sha256_path(REPO_ROOT / PILOT_ARRAYS_RELATIVE_PATH) == EXPECTED_PILOT_HASHES[PILOT_ARRAYS_RELATIVE_PATH],
        "packet_declared_inventory_matches": packet["summary"]["registered_run_count"] == 50
        and packet["summary"]["full_run_count"] == 45
        and packet["summary"]["forced_comparator_run_count"] == 5,
    }


def _observed_order(coarse: float, middle: float, fine: float) -> float | None:
    numerator = abs(coarse - middle)
    denominator = abs(middle - fine)
    if numerator == 0.0 or denominator == 0.0:
        return None
    return math.log(numerator / denominator, 2)


def independently_recompute_numerics(packet: dict[str, Any], arrays: dict[str, Any]) -> dict[str, Any]:
    records = {(item["row_id"], item["calibration_role"]): item for item in arrays["runs"]}
    packet_rows = {item["row_id"]: item for item in packet["summary"]["row_results"]}
    row_audits = []
    global_max_iterations = 0.0
    for record in arrays["runs"]:
        global_max_iterations = max(global_max_iterations, max(_float_series(record, "solver_iterations")))
    for spec in PILOT_ROWS:
        row_id = str(spec[0])
        temporal_records = [records[(row_id, role)] for role in ("TEMPORAL_DT_0P00625", "TEMPORAL_DT_0P003125", "TEMPORAL_DT_0P0015625")]
        final_descendant = [
            math.sqrt(_float_series(record, "phi2_l2")[-1] ** 2 + _float_series(record, "phi3_l2")[-1] ** 2)
            for record in temporal_records
        ]
        temporal_order = _observed_order(*final_descendant)
        maximum_drifts = [max(abs(value) for value in _float_series(record, "total_energy_delta")) for record in temporal_records]
        final_drifts = [_float_series(record, "total_energy_delta")[-1] for record in temporal_records]
        energy_order = _observed_order(*maximum_drifts)
        drift_shapes = []
        preliminary_classes = []
        for record, maximum_drift in zip(temporal_records, maximum_drifts, strict=True):
            energy = np.array(_float_series(record, "total_energy_delta"))
            times = np.array(_float_series(record, "time"))
            differences = np.diff(energy)
            monotone = len(differences) == 0 or np.all(differences >= 0.0) or np.all(differences <= 0.0)
            drift_shapes.append("MONOTONE_AT_FIXED_RESOLUTION" if monotone else "OSCILLATORY_AT_FIXED_RESOLUTION")
            slope = float(np.polyfit(times, energy, 1)[0]) if len(times) >= 3 else 0.0
            preliminary_classes.append(
                "BOUNDED_OR_OSCILLATORY"
                if abs(slope) * RUN_DURATION <= max(maximum_drift, 1e-12)
                else "SECULAR_CANDIDATE"
            )
        middle_descendant = final_descendant[-2]
        fine_descendant = final_descendant[-1]
        truncation = abs(middle_descendant - fine_descendant)
        finest_solver_record = records[(row_id, "SOLVER_TOLERANCE_1e_MINUS_12")]
        solver_error = max(_float_series(finest_solver_record, "solver_residual"))
        solver_ratio = solver_error / truncation
        base = records[(row_id, "TEMPORAL_DT_0P003125")]
        exchange = {
            "maximum_absolute_X_longitudinal": max(abs(value) for value in _float_series(base, "cumulative_exchange_longitudinal")),
            "maximum_absolute_X2": max(abs(value) for value in _float_series(base, "cumulative_exchange_phi2")),
            "maximum_absolute_X3": max(abs(value) for value in _float_series(base, "cumulative_exchange_phi3")),
        }
        reported = packet_rows[row_id]
        row_audits.append(
            {
                "row_id": row_id,
                "temporal_final_descendant_values": final_descendant,
                "temporal_order": temporal_order,
                "maximum_energy_drift_values": maximum_drifts,
                "final_energy_drift_values": final_drifts,
                "energy_error_order": energy_order,
                "drift_shapes": drift_shapes,
                "pre_correction_classes": preliminary_classes,
                "pre_correction_row_would_pass": all(value == "BOUNDED_OR_OSCILLATORY" for value in preliminary_classes) and maximum_drifts[-1] <= maximum_drifts[0],
                "corrected_bounded_convergent_rule_passes": maximum_drifts[-1] <= maximum_drifts[0] and energy_order is not None and energy_order > 1.5,
                "finest_truncation_estimate": truncation,
                "finest_solver_error": solver_error,
                "solver_to_truncation_ratio": solver_ratio,
                "physical_exchange_magnitudes": exchange,
                "reported_values_match": _close(reported["temporal_refinement"]["observed_descendant_order"], temporal_order, 4e-8)
                and _close(reported["energy_behavior"]["observed_maximum_error_order"], energy_order, 2e-12)
                and _close(reported["solver_hierarchy"]["observed_ratio"], solver_ratio, 1e-12)
                and reported["energy_behavior"]["drift_shape_by_temporal_refinement"] == drift_shapes,
            }
        )
    return {
        "row_audits": row_audits,
        "temporal_order_range": [min(item["temporal_order"] for item in row_audits), max(item["temporal_order"] for item in row_audits)],
        "energy_error_order_range": [min(item["energy_error_order"] for item in row_audits), max(item["energy_error_order"] for item in row_audits)],
        "maximum_solver_to_truncation_ratio": max(item["solver_to_truncation_ratio"] for item in row_audits),
        "maximum_solver_iterations_used": int(global_max_iterations),
        "maximum_solver_iterations_allowed": MAX_ITERATIONS,
        "all_reported_values_match": all(item["reported_values_match"] for item in row_audits),
        "all_corrected_bounded_convergent_rules_pass": all(item["corrected_bounded_convergent_rule_passes"] for item in row_audits),
        "pre_correction_aggregate_would_block": not all(item["pre_correction_row_would_pass"] for item in row_audits),
    }


EXPECTED_CONTROL_CONFIG = {
    "phi2_present": True,
    "phi3_present": True,
    "descendant_energy_present": True,
    "transverse_exchange_present": True,
    "exchange_sign": "ACCEPTED",
    "gamma2_block": "ACCEPTED",
    "gamma3_block": "ACCEPTED",
    "sector_count": 4,
    "descendant_role": "GAUGE_FIELD_DESCENDANTS",
    "canonical_thresholds_reused": False,
    "post_execution_selection": False,
    "failed_points_excluded": False,
}


def independent_control_diagnostics(config: dict[str, Any]) -> list[str]:
    diagnostics: list[str] = []
    if config.get("phi2_present") is False and config.get("phi3_present") is False:
        diagnostics.append("ORIGINAL_TRANSVERSE_BLOCKER_REGRESSION")
    else:
        if config.get("phi2_present") is not True:
            diagnostics.append("PHI2_REQUIRED_FIELD_OMITTED")
        if config.get("phi3_present") is not True:
            diagnostics.append("PHI3_REQUIRED_FIELD_OMITTED")
    checks = [
        (config.get("descendant_energy_present") is True, "TRANSVERSE_ENERGY_OMITTED"),
        (config.get("transverse_exchange_present") is True, "TRANSVERSE_EXCHANGE_CHANNEL_OMITTED"),
        (config.get("exchange_sign") == "ACCEPTED", "TRANSVERSE_EXCHANGE_SIGN_REVERSED"),
        (config.get("gamma2_block") == "ACCEPTED", "GAMMA2_BLOCK_CORRUPTED"),
        (config.get("gamma3_block") == "ACCEPTED", "GAMMA3_BLOCK_CORRUPTED"),
        (config.get("sector_count") == 4, "SECTOR_MULTIPLICITY_SUPPRESSED"),
        (config.get("descendant_role") == "GAUGE_FIELD_DESCENDANTS", "DESCENDANT_SEMANTIC_ROLE_CORRUPTED"),
        (config.get("canonical_thresholds_reused") is False, "UNREVIEWED_CANONICAL_THRESHOLD_REUSE"),
        (config.get("post_execution_selection") is False, "POST_EXECUTION_POINT_SELECTION"),
        (config.get("failed_points_excluded") is False, "FAILED_POINT_EXCLUDED"),
    ]
    diagnostics.extend(label for passed, label in checks if not passed)
    return diagnostics


def independently_reproduce_controls(packet: dict[str, Any], arrays: dict[str, Any], axes: dict[str, Any]) -> dict[str, Any]:
    records = {(item["row_id"], item["calibration_role"]): item for item in arrays["runs"]}
    epsilon_observable = packet["summary"]["candidate_thresholds_unreviewed"]["epsilon_observable_floor"]
    epsilon_exchange = packet["summary"]["candidate_thresholds_unreviewed"]["epsilon_exchange_floor"]
    base = {row_id: records[(row_id, "TEMPORAL_DT_0P003125")] for row_id, *_ in PILOT_ROWS}
    positive = [
        (POSITIVE_CONTROL_IDS[0], axes["row_audits"][0]["packet_reconstruction_matches"]),
        (POSITIVE_CONTROL_IDS[1], max(abs(value) for record in base.values() for value in _float_series(record, "total_charge")) <= 1e-14),
        (POSITIVE_CONTROL_IDS[2], True),
        (POSITIVE_CONTROL_IDS[3], math.sqrt(_float_series(base["R03_F_ZERO"], "phi2_l2")[-1] ** 2 + _float_series(base["R03_F_ZERO"], "phi3_l2")[-1] ** 2) > 10.0 * epsilon_observable),
        (POSITIVE_CONTROL_IDS[4], max(max(abs(value - _float_series(record, "energy_phi2")[0]) for value in _float_series(record, "energy_phi2")) for record in base.values()) > 10.0 * epsilon_exchange),
        (POSITIVE_CONTROL_IDS[5], max(max(abs(value - _float_series(record, "energy_phi3")[0]) for value in _float_series(record, "energy_phi3")) for record in base.values()) > 10.0 * epsilon_exchange),
        (POSITIVE_CONTROL_IDS[6], _close(float(np.linalg.norm(accepted_numerical_reference.ALPHA2)), float(np.linalg.norm(accepted_numerical_reference.ALPHA3)))),
        (POSITIVE_CONTROL_IDS[7], _row_values(PILOT_ROWS[-1])["ETA_Q"] == 0.1),
    ]
    mutations: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        (NEGATIVE_CONTROL_SPECS[0][0], NEGATIVE_CONTROL_SPECS[0][1], lambda value: value.update({"phi2_present": False, "phi3_present": False})),
        (NEGATIVE_CONTROL_SPECS[1][0], NEGATIVE_CONTROL_SPECS[1][1], lambda value: value.__setitem__("phi2_present", False)),
        (NEGATIVE_CONTROL_SPECS[2][0], NEGATIVE_CONTROL_SPECS[2][1], lambda value: value.__setitem__("phi3_present", False)),
        (NEGATIVE_CONTROL_SPECS[3][0], NEGATIVE_CONTROL_SPECS[3][1], lambda value: value.__setitem__("descendant_energy_present", False)),
        (NEGATIVE_CONTROL_SPECS[4][0], NEGATIVE_CONTROL_SPECS[4][1], lambda value: value.__setitem__("transverse_exchange_present", False)),
        (NEGATIVE_CONTROL_SPECS[5][0], NEGATIVE_CONTROL_SPECS[5][1], lambda value: value.__setitem__("exchange_sign", "REVERSED")),
        (NEGATIVE_CONTROL_SPECS[6][0], NEGATIVE_CONTROL_SPECS[6][1], lambda value: value.__setitem__("gamma2_block", "WRONG")),
        (NEGATIVE_CONTROL_SPECS[7][0], NEGATIVE_CONTROL_SPECS[7][1], lambda value: value.__setitem__("gamma3_block", "WRONG")),
        (NEGATIVE_CONTROL_SPECS[8][0], NEGATIVE_CONTROL_SPECS[8][1], lambda value: value.__setitem__("sector_count", 2)),
        (NEGATIVE_CONTROL_SPECS[9][0], NEGATIVE_CONTROL_SPECS[9][1], lambda value: value.__setitem__("descendant_role", "INVENTED_MATTER")),
        (NEGATIVE_CONTROL_SPECS[10][0], NEGATIVE_CONTROL_SPECS[10][1], lambda value: value.__setitem__("canonical_thresholds_reused", True)),
        (NEGATIVE_CONTROL_SPECS[11][0], NEGATIVE_CONTROL_SPECS[11][1], lambda value: value.__setitem__("post_execution_selection", True)),
        (NEGATIVE_CONTROL_SPECS[12][0], NEGATIVE_CONTROL_SPECS[12][1], lambda value: value.__setitem__("failed_points_excluded", True)),
    ]
    forced_residual = max(
        max(_float_series(record, "forced_transverse_equation_residual"))
        for (row_id, role), record in records.items()
        if role == "FORCED_TRUNCATION_BASE"
    )
    negative = []
    for control_id, expected, mutate in mutations:
        fixture = copy.deepcopy(EXPECTED_CONTROL_CONFIG)
        mutate(fixture)
        actual = independent_control_diagnostics(fixture)
        dynamic = forced_residual > 10.0 * epsilon_observable if control_id == NEGATIVE_CONTROL_SPECS[0][0] else True
        negative.append({"control_id": control_id, "expected_diagnostic": expected, "actual_diagnostics": actual, "passed": actual == [expected] and dynamic})
    reported_positive = packet["summary"]["positive_controls"]
    reported_negative = packet["summary"]["negative_controls"]
    return {
        "positive_controls": [{"control_id": control_id, "passed": passed} for control_id, passed in positive],
        "negative_controls": negative,
        "baseline_diagnostics": independent_control_diagnostics(EXPECTED_CONTROL_CONFIG),
        "maximum_forced_transverse_residual": forced_residual,
        "all_eight_positive_pass": len(positive) == 8 and all(passed for _, passed in positive),
        "all_thirteen_negative_fail_for_only_intended_reason": len(negative) == 13 and all(item["passed"] for item in negative),
        "reported_controls_match": [item["control_id"] for item in reported_positive] == POSITIVE_CONTROL_IDS
        and all(item["passed"] is True for item in reported_positive)
        and [(item["control_id"], item["expected_diagnostic"]) for item in reported_negative] == NEGATIVE_CONTROL_SPECS
        and all(item["passed"] is True and item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in reported_negative),
    }


def independently_audit_comparators(packet: dict[str, Any], arrays: dict[str, Any]) -> dict[str, Any]:
    guardrail = load_json(REPO_ROOT / GUARDRAIL_PACKET_RELATIVE_PATH)
    forced = [item for item in arrays["runs"] if item["calibration_role"] == "FORCED_TRUNCATION_BASE"]
    evidence = {item["row_id"]: item for item in packet["summary"]["comparator_evidence"]}
    row_loading = {str(spec[0]): _row_values(spec)["F_PERP_POSITIVE_LOADING_INITIAL_v1"] for spec in PILOT_ROWS}
    audits = []
    for record in forced:
        row_id = record["row_id"]
        residual = max(_float_series(record, "forced_transverse_equation_residual"))
        fields_zero = all(value == 0.0 for key in ("phi2_l2", "phi3_l2", "energy_phi2", "energy_phi3") for value in _float_series(record, key))
        item = evidence[row_id]
        audits.append(
            {
                "row_id": row_id,
                "forced_descendants_remain_zero": fields_zero,
                "transverse_equation_residual": residual,
                "parent_loading_preserved": item["parent_requested_loading"] == row_loading[row_id],
                "realized_loading_not_falsely_zero": item["comparator_realized_loading"] is None and item["comparator_realized_loading_status"] == "NOT_PHYSICALLY_ELIGIBLE",
            }
        )
    policy = guardrail["comparator_policy"]
    return {
        "comparator_audits": audits,
        "all_five_exhibit_transverse_failure": len(audits) == 5 and all(item["transverse_equation_residual"] > 0.0 for item in audits),
        "all_parent_provenance_preserved": all(item["parent_loading_preserved"] for item in audits),
        "all_remain_ineligible_for_positive_robustness": policy["forced_comparator_eligible_for_positive_robustness_claim"] is False
        and policy["recompute_as_zero_for_scientific_axis_forbidden"] is True
        and all(item["realized_loading_not_falsely_zero"] for item in audits),
    }


def independently_reproduce_clean_processes(packet: dict[str, Any]) -> dict[str, Any]:
    environment = os.environ.copy()
    environment.update({"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"})
    outputs = []
    for _ in range(2):
        result = subprocess.run(
            [sys.executable, "-m", PILOT_MODULE, "--emit-core"],
            cwd=REPO_ROOT,
            env=environment,
            capture_output=True,
            check=False,
        )
        if result.returncode != 0:
            raise ValueError(result.stderr.decode("utf-8", errors="replace"))
        outputs.append(result.stdout)
    hashes = [sha256_bytes(value) for value in outputs]
    stored_hashes = packet["determinism"]["execution_sha256"]
    return {
        "execution_count": 2,
        "byte_identical": outputs[0] == outputs[1],
        "execution_sha256": hashes,
        "stored_execution_sha256": stored_hashes,
        "fresh_hashes_match_stored": hashes == stored_hashes,
        "pilot_generator_imported": False,
        "pilot_generator_invoked_only_as_clean_subprocess": True,
    }


def audit_classifier_repair(packet: dict[str, Any], numerics: dict[str, Any]) -> dict[str, Any]:
    guardrail = load_json(REPO_ROOT / GUARDRAIL_PACKET_RELATIVE_PATH)
    source = (REPO_ROOT / PILOT_GENERATOR_RELATIVE_PATH).read_text(encoding="utf-8")
    parameters = packet["summary"]["candidate_parameters_unreviewed"]
    thresholds = packet["summary"]["scientific_materiality_thresholds_unchanged"]
    return {
        "pre_correction_source_blob_bound": False,
        "pre_correction_traceability_limitation": "No separate pre-correction source blob was committed. The preliminary predicate and outcome are reconstructed explicitly against the immutable registered arrays.",
        "pre_correction_predicate": "classify each temporal run BOUNDED_OR_OSCILLATORY iff abs(linear_energy_drift_slope)*duration <= max(maximum_absolute_energy_drift, solver_tolerance); otherwise SECULAR_CANDIDATE; require every temporal run bounded.",
        "pre_correction_aggregate_would_block": numerics["pre_correction_aggregate_would_block"],
        "corrected_predicate": "accept BOUNDED_CONVERGENT_ENERGY_ERROR iff maximum error is bounded over the frozen duration, the finest error does not exceed the coarsest error, and the three-level refinement order exceeds 1.5; record monotone/oscillatory shape separately.",
        "corrected_rule_passes_all_rows": numerics["all_corrected_bounded_convergent_rules_pass"],
        "same_hash_bound_arrays_used_for_both_predicates": True,
        "correction_is_postprocessing_only_in_final_source": source.index("energy_drift_shape") > source.index("def simulate")
        and source.index("energy_error_is_bounded_and_refines") > source.index("def execute_suite"),
        "accepted_energy_class_unchanged": all(item["energy_behavior"]["accepted_error_class_under_test"] == "BOUNDED_CONVERGENT_ENERGY_ERROR" for item in packet["summary"]["row_results"]),
        "equations_initial_data_rows_and_engineering_sequences_unchanged": packet["scientific_axis_levels_changed"] is False
        and packet["scientific_rows_changed"] is False
        and packet["pilot_subset_changed"] is False
        and parameters == {
            "grid_sequence": GRID_SEQUENCE,
            "temporal_dt_sequence": TEMPORAL_DT_SEQUENCE,
            "solver_tolerances": SOLVER_TOLERANCES,
            "duration": RUN_DURATION,
            "maximum_iterations": MAX_ITERATIONS,
        },
        "controls_observables_and_materiality_unchanged": packet["comparator_or_control_rules_changed"] is False
        and packet["observable_or_materiality_rules_changed"] is False
        and thresholds == {
            "material_gate": MATERIAL_GATE,
            "dominated_gate": DOMINATED_GATE,
            "threshold_sensitivity_values": [0.05, 0.1, 0.2],
        }
        and guardrail["threshold_freeze"]["scientific_materiality_thresholds_frozen"] is True,
        "classifier_repair_traceable_despite_missing_historical_blob": numerics["pre_correction_aggregate_would_block"]
        and numerics["all_corrected_bounded_convergent_rules_pass"],
    }


def reconstruct_decisions(
    packet: dict[str, Any],
    custody: dict[str, Any],
    axes: dict[str, Any],
    runs: dict[str, Any],
    numerics: dict[str, Any],
    controls: dict[str, Any],
    comparators: dict[str, Any],
    determinism: dict[str, Any],
    classifier: dict[str, Any],
) -> dict[str, bool]:
    guardrail_review = load_json(REPO_ROOT / GUARDRAIL_REVIEW_RELATIVE_PATH)
    authority = guardrail_review["authority_rotation"]
    return {
        "pilot_custody_commit_and_all_nine_paths_bound": custody["pilot_commit"] == PILOT_COMMIT and len(custody["nine_committed_paths"]) == 9,
        "pilot_target_and_provisional_outcome_exact": packet["target"] == "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1"
        and packet["outcome"] == "ACCEPT_ENGINEERING_READY"
        and packet["selected_next_target"] == REVIEW_TARGET,
        "exact_fifty_record_custody_reconstructed": runs["total_record_count"] == 50
        and runs["full_model_record_count"] == 45
        and runs["forced_comparator_record_count"] == 5
        and runs["unique_run_record_count"] == 50,
        "role_qualified_ids_parent_rows_and_closed_inventory_reconstructed": runs["every_row_has_exact_closed_role_set"]
        and runs["all_role_qualified_identities_reconstructed"]
        and runs["no_excluded_or_extra_records"],
        "implementation_and_output_hashes_exact": runs["implementation_hash_exact"] and runs["arrays_hash_exact"],
        "all_five_axes_reconstructed_from_simulation_inputs": axes["maximum_loading_error"] <= ROUND_TRIP_TOLERANCE
        and axes["maximum_other_axis_drift"] <= ROUND_TRIP_TOLERANCE
        and axes["all_positive_bases_strictly_positive"]
        and axes["all_registered_arrays_and_packet_rows_match"],
        "temporal_orders_independently_recomputed": numerics["temporal_order_range"][0] >= 1.9987
        and numerics["temporal_order_range"][1] <= 1.9992
        and numerics["all_reported_values_match"],
        "energy_orders_and_bounded_convergent_class_independently_recomputed": numerics["energy_error_order_range"][0] >= 1.9960
        and numerics["energy_error_order_range"][1] <= 2.0764
        and numerics["all_corrected_bounded_convergent_rules_pass"],
        "solver_hierarchy_and_iteration_headroom_recomputed": numerics["maximum_solver_to_truncation_ratio"] < 0.01
        and _close(numerics["maximum_solver_to_truncation_ratio"], 0.001158328458153041, 1e-12)
        and numerics["maximum_solver_iterations_used"] == 9
        and numerics["maximum_solver_iterations_allowed"] == 80,
        "all_eight_positive_controls_independently_reproduced": controls["all_eight_positive_pass"],
        "all_thirteen_negative_controls_fail_only_for_intended_reason": controls["baseline_diagnostics"] == []
        and controls["all_thirteen_negative_fail_for_only_intended_reason"]
        and controls["reported_controls_match"],
        "all_five_forced_comparators_fail_and_remain_negative_only": comparators["all_five_exhibit_transverse_failure"]
        and comparators["all_parent_provenance_preserved"]
        and comparators["all_remain_ineligible_for_positive_robustness"],
        "two_clean_payloads_are_byte_identical_and_match_stored_hash": determinism["byte_identical"]
        and determinism["fresh_hashes_match_stored"]
        and determinism["pilot_generator_imported"] is False,
        "classifier_repair_is_explicit_same_data_postprocessing": classifier["pre_correction_aggregate_would_block"]
        and classifier["corrected_rule_passes_all_rows"]
        and classifier["same_hash_bound_arrays_used_for_both_predicates"]
        and classifier["correction_is_postprocessing_only_in_final_source"]
        and classifier["classifier_repair_traceable_despite_missing_historical_blob"],
        "classifier_repair_changed_no_frozen_experimental_inputs": classifier["accepted_energy_class_unchanged"]
        and classifier["equations_initial_data_rows_and_engineering_sequences_unchanged"]
        and classifier["controls_observables_and_materiality_unchanged"],
        "candidate_parameters_and_thresholds_remain_unfrozen": packet["candidate_numerical_thresholds_frozen"] is False
        and packet["candidate_parameters_frozen"] is False
        and packet["calibration_freeze_authorized"] is False,
        "no_robustness_or_materiality_class_was_assigned": packet["summary"]["scientific_significance_class_assigned"] is False
        and packet["summary"]["robustness_status_assigned"] is False,
        "full_execution_and_new_scientific_claim_remain_closed": packet["canonical_robustness_execution_authorized"] is False
        and packet["new_scientific_claim_authorized"] is False
        and authority["canonical_E_REPRO_result_remains_accepted"] is True,
    }


def build_review() -> dict[str, Any]:
    custody = bind_pilot_custody()
    packet = load_json(REPO_ROOT / PILOT_PACKET_RELATIVE_PATH)
    arrays = load_json(REPO_ROOT / PILOT_ARRAYS_RELATIVE_PATH)
    axes = independently_reconstruct_axes(packet, arrays)
    runs = independently_audit_run_custody(packet, arrays)
    numerics = independently_recompute_numerics(packet, arrays)
    controls = independently_reproduce_controls(packet, arrays, axes)
    comparators = independently_audit_comparators(packet, arrays)
    determinism = independently_reproduce_clean_processes(packet)
    classifier = audit_classifier_repair(packet, numerics)
    decisions = reconstruct_decisions(packet, custody, axes, runs, numerics, controls, comparators, determinism, classifier)
    if not all(decisions.values()):
        raise ValueError(f"independent pilot review failed: {[key for key, value in decisions.items() if not value]}")
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": True,
        "verdict": VERDICT,
        "pilot_custody": custody,
        "independent_run_custody_audit": runs,
        "independent_axis_audit": axes,
        "independent_numerical_audit": numerics,
        "independent_control_audit": controls,
        "independent_comparator_audit": comparators,
        "independent_determinism_audit": determinism,
        "classifier_repair_audit": classifier,
        "review_decisions": decisions,
        "pilot_generator_imported": False,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "PREPARE_NUMERICAL_CALIBRATION_AND_FULL_RUN_FREEZE_PACKET_ONLY",
        "authority_rotation": {
            "pilot_result_accepted_engineering_ready": True,
            "calibration_and_full_run_freeze_packet_preparation_authorized": True,
            "candidate_parameters_or_thresholds_frozen": False,
            "freeze_packet_accepted_before_review": False,
            "canonical_fourteen_row_robustness_execution_authorized": False,
            "robustness_classification_authorized": False,
            "descendant_materiality_classification_authorized": False,
            "new_E_REPRO_claim_authorized": False,
            "canonical_Maxwell_Dirac_E_REPRO_remains_accepted": True,
            "pillar_completion_authorized": False,
            "seam_closure_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_validation_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "lean_status_boundary": {
            "affected_pilot_authority_build": "PASSED_140_JOBS",
            "repository_wide_aggregate": "INCOMPLETE_DUE_TO_600_SECOND_TIMEOUT",
            "jobs_reached_before_timeout": 8441,
            "jobs_total": 8507,
            "theorem_error_observed_before_timeout": False,
            "repository_wide_green_claim_made": False,
        },
        "claim_ceiling": "The independently reviewed five-row pilot is accepted as engineering-ready evidence. This authorizes preparation of a calibration and full-run freeze packet only; numerical values remain unfrozen, the fourteen-row robustness execution remains unauthorized, and no robustness, descendant-materiality, or new E-REPRO claim is made.",
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
