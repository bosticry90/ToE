from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import subprocess
import sys
import unicodedata
from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v1.json"
RUN_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-RUN-MATRIX-v1.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-MANIFEST-v1.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v1.json"
CLASSIFIER_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v1.py"
CLASSIFIER_SHA256 = "d71191f45e4cbfaa501c5a20e0e1e8213835f5b30c7a2760f56fceea1d958062"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
RUN_MATRIX_PATH = REPO_ROOT / RUN_MATRIX_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

GUARDRAIL_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v1.json"
GUARDRAIL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260714_v1.json"
PILOT_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1.py"
PILOT_TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1.py"
PILOT_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
PILOT_ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
PILOT_MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-MANIFEST-v1.json"
PILOT_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_20260714_v1.json"
PILOT_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessNonAuthoritativePilotV1.lean"
PILOT_REVIEW_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1_result_review.py"
PILOT_REVIEW_TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1_result_review.py"
PILOT_REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_RESULT_REVIEW_20260714_v1.json"
PILOT_REVIEW_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessNonAuthoritativePilotV1ResultReview.lean"

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1_result"
POST_ACCEPTANCE_TARGET = "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v1"
BLOCKED_TARGET = "repair_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_v1"
RUN_MATRIX_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_RUN_MATRIX_v1"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_MANIFEST_v1"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v1"
PILOT_REVIEW_COMMIT = "1004b0a2203b5c4abdfd6a120d23372518b8f631"
PILOT_REVIEW_PARENT = "f8f896279f70f464ef5cc927093d242874cd0eef"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

INPUT_HASHES = {
    GUARDRAIL_PACKET_RELATIVE_PATH: "54f3c8137986db1ba1bf7cc1a9e0ffade11ed7b6fdf480bf103cdd6b13d964f1",
    GUARDRAIL_REVIEW_RELATIVE_PATH: "a2c1de4f699bf0a2fc1cb38ce0e72b7682df5c0757fa61692f1d32b8e236832e",
    PILOT_GENERATOR_RELATIVE_PATH: "05e7015499e3d15bc172840ac637fd0fa86b6c50f87489d6b555657ac290adb6",
    PILOT_TEST_RELATIVE_PATH: "be2b00a7fda37a79e2dd1b904d367a1277914d40a525a21de258903c6d3c1a71",
    PILOT_PACKET_RELATIVE_PATH: "d8c1f75c955b9a368159bd579f7d886523e8c66b0e611a6e6290a179422cf03a",
    PILOT_ARRAYS_RELATIVE_PATH: "5ffaca2e6e07e95ef1bb1b1451b2bda01eab355e55294a6dd51b2ffe8ecf8e8e",
    PILOT_MANIFEST_RELATIVE_PATH: "51226ec5af368967c895bb5dc9c4333f7ee3d89756de4fcc1c5f82600161ab93",
    PILOT_REPORT_RELATIVE_PATH: "a898245a13b24629af5c705c47710b8672f32dc6aded27073601e612efa379cb",
    PILOT_LEAN_RELATIVE_PATH: "b4001f3f089175bbc09be7aa5cc84249876b83caa1b2024e7f513ba6789c5fb7",
    PILOT_REVIEW_GENERATOR_RELATIVE_PATH: "9a64587b7884211e85094a752145ab669925efe34267138f3f27b078b947cebe",
    PILOT_REVIEW_TEST_RELATIVE_PATH: "39172afb23df903ab9fa70768e522903491849fc427ae0a2c0ee1b993e47cc7f",
    PILOT_REVIEW_REPORT_RELATIVE_PATH: "e2e55a07b929f42601653e4a0f6eed5ecae7dc765441277fbc2ef62b253b302d",
    PILOT_REVIEW_LEAN_RELATIVE_PATH: "fa2546fa8c091df601de5e2af80298dcb2d348d4197978b45561c55e1820c948",
}

PRIMARY_PARAMETERS = {
    "grid_size": 32,
    "time_step": 0.0015625,
    "duration": 0.05,
    "solver_tolerance": 1e-12,
    "maximum_iterations": 80,
}
GRID_SEQUENCE = [8, 16, 32]
TEMPORAL_DT_SEQUENCE = [0.00625, 0.003125, 0.0015625]
SOLVER_TOLERANCES = [1e-8, 1e-10, 1e-12]
OUTPUT_ROOT = "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_v1"

EQUATION_RESIDUAL_KEYS = (
    "longitudinal_Maxwell_residual",
    "phi2_wave_residual",
    "phi3_wave_residual",
    "Dirac_plus_sector1_residual",
    "Dirac_plus_sector2_residual",
    "Dirac_minus_sector1_residual",
    "Dirac_minus_sector2_residual",
    "adjoint_plus_sector1_residual",
    "adjoint_plus_sector2_residual",
    "adjoint_minus_sector1_residual",
    "adjoint_minus_sector2_residual",
)
METRIC_SERIES = {
    "maximum_solver_residual": "solver_residual",
    "maximum_Gauss_residual": "gauss_residual",
    "maximum_continuity_residual": "continuity_residual",
    "maximum_link_norm_error": "link_norm_error",
    "maximum_energy_drift": "total_energy_delta",
    "maximum_exchange_longitudinal_residual": "exchange_longitudinal_residual",
    "maximum_exchange_phi2_residual": "exchange_phi2_residual",
    "maximum_exchange_phi3_residual": "exchange_phi3_residual",
    "maximum_exchange_combined_residual": "exchange_combined_residual",
    **{f"maximum_{key}": key for key in EQUATION_RESIDUAL_KEYS},
}
OBSERVABLE_FLOOR_KEYS = (
    "matter_density_l2",
    "longitudinal_electric_field_l2",
    "matter_energy",
    "total_source_current_l2",
    "phi2_l2",
    "phi3_l2",
    "transverse_source_l2",
)
EXCHANGE_FLOOR_KEYS = (
    "cumulative_exchange_longitudinal",
    "cumulative_exchange_phi2",
    "cumulative_exchange_phi3",
)


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


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


def validate_authority() -> None:
    if git_output("rev-parse", f"{PILOT_REVIEW_COMMIT}^").decode().strip() != PILOT_REVIEW_PARENT:
        raise ValueError("pilot-review parent mismatch")
    if subprocess.run(
        ["git", "merge-base", "--is-ancestor", PILOT_REVIEW_COMMIT, "HEAD"],
        cwd=REPO_ROOT,
        check=False,
    ).returncode != 0:
        raise ValueError("accepted pilot-review commit is not an ancestor of HEAD")
    for relative_path, digest in INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"accepted input hash mismatch: {relative_path}")
    review = load_json(REPO_ROOT / PILOT_REVIEW_REPORT_RELATIVE_PATH)
    rotation = review.get("authority_rotation", {})
    if not (
        review.get("accepted") is True
        and review.get("verdict") == "ACCEPT_ENGINEERING_READY"
        and review.get("selected_next_target") == TARGET
        and rotation.get("calibration_and_full_run_freeze_packet_preparation_authorized") is True
        and rotation.get("candidate_parameters_or_thresholds_frozen") is False
        and rotation.get("canonical_fourteen_row_robustness_execution_authorized") is False
    ):
        raise ValueError("accepted pilot review does not authorize this preparation")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        raise ValueError("Prompt.txt content changed from the protected scientific input")
    if sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH) != CLASSIFIER_SHA256:
        raise ValueError("proposed frozen classifier implementation changed")


def round_up_one_significant(value: float) -> float:
    if value <= 0.0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return math.ceil(value / scale) * scale


def floor_to_half(value: float) -> float:
    return math.floor(2.0 * value) / 2.0


def _float_series(record: dict[str, Any], key: str) -> list[float]:
    return [float(value) for value in record["series"][key]]


def threshold_provenance(
    pilot_packet: dict[str, Any], arrays: dict[str, Any], row_ids: list[str]
) -> list[dict[str, Any]]:
    records = arrays["runs"]
    candidates = pilot_packet["summary"]["candidate_thresholds_unreviewed"]
    all_run_ids = [record["run_record_id"] for record in records]
    entries: list[dict[str, Any]] = []
    for threshold_id, series_key in METRIC_SERIES.items():
        per_record = {
            record["run_record_id"]: max(abs(value) for value in _float_series(record, series_key))
            for record in records
        }
        measured = max(per_record.values())
        recomputed = round_up_one_significant(2.0 * measured)
        candidate = float(candidates[threshold_id])
        if recomputed != candidate:
            raise ValueError(f"registered arrays do not reconstruct {threshold_id}: {recomputed} != {candidate}")
        extremal = [run_id for run_id, value in per_record.items() if value == measured]
        category = (
            "SOLVER"
            if threshold_id == "maximum_solver_residual"
            else "ENERGY"
            if threshold_id == "maximum_energy_drift"
            else "CONSTRAINT"
            if threshold_id in {"maximum_Gauss_residual", "maximum_continuity_residual", "maximum_link_norm_error"}
            else "EQUATION_OR_EXCHANGE_RESIDUAL"
        )
        entries.append(
            {
                "threshold_id": threshold_id,
                "pilot_source_run_ids": all_run_ids,
                "extremal_source_run_ids": extremal,
                "measured_pilot_value": measured,
                "generation_formula": "round_up_one_significant(2 * maximum_over_all_50_registered_pilot_records)",
                "rounding_rule": "multiply the registered maximum by two, then round upward to one significant digit",
                "candidate_frozen_threshold": candidate,
                "recomputed_threshold": recomputed,
                "eligible_scientific_row_ids": row_ids,
                "meaning": f"maximum admitted {threshold_id} across the preregistered run role to which the metric applies",
                "failure_classification": f"NUMERICALLY_BLOCKED:{category}",
            }
        )

    by_row_role = {(item["row_id"], item["calibration_role"]): item for item in records}
    floor_specs = (
        ("epsilon_observable_floor", OBSERVABLE_FLOOR_KEYS),
        ("epsilon_exchange_floor", EXCHANGE_FLOOR_KEYS),
    )
    for threshold_id, keys in floor_specs:
        per_row: dict[str, float] = {}
        source_ids: list[str] = []
        for row_id in pilot_packet["summary"]["row_results"]:
            pilot_row_id = row_id["row_id"]
            medium = by_row_role[(pilot_row_id, "SOLVER_TOLERANCE_1e_MINUS_10")]
            fine = by_row_role[(pilot_row_id, "SOLVER_TOLERANCE_1e_MINUS_12")]
            source_ids.extend([medium["run_record_id"], fine["run_record_id"]])
            per_row[pilot_row_id] = max(
                abs(left - right)
                for key in keys
                for left, right in zip(
                    _float_series(medium, key),
                    _float_series(fine, key),
                    strict=True,
                )
            )
        measured = max(per_row.values())
        recomputed = round_up_one_significant(2.0 * measured)
        candidate = float(candidates[threshold_id])
        if recomputed != candidate:
            raise ValueError(f"registered arrays do not reconstruct {threshold_id}: {recomputed} != {candidate}")
        extremal_rows = [row_id for row_id, value in per_row.items() if value == measured]
        extremal_ids = [
            by_row_role[(row_id, role)]["run_record_id"]
            for row_id in extremal_rows
            for role in ("SOLVER_TOLERANCE_1e_MINUS_10", "SOLVER_TOLERANCE_1e_MINUS_12")
        ]
        entries.append(
            {
                "threshold_id": threshold_id,
                "pilot_source_run_ids": source_ids,
                "extremal_source_run_ids": extremal_ids,
                "measured_pilot_value": measured,
                "generation_formula": "round_up_one_significant(2 * maximum_medium_vs_fine_solver_series_difference_across_five_pilot_rows)",
                "rounding_rule": "multiply the registered maximum by two, then round upward to one significant digit",
                "candidate_frozen_threshold": candidate,
                "recomputed_threshold": recomputed,
                "eligible_scientific_row_ids": row_ids,
                "meaning": "independently calibrated denominator floor; it measures numerical distinguishability and never scientific materiality",
                "failure_classification": "NUMERICALLY_BLOCKED:UNRESOLVED_SIGNAL_FLOOR",
            }
        )
    return sorted(entries, key=lambda item: item["threshold_id"])


def convergence_thresholds(pilot_packet: dict[str, Any]) -> list[dict[str, Any]]:
    rows = pilot_packet["summary"]["row_results"]
    specs = (
        (
            "minimum_spatial_descendant_order",
            [float(row["spatial_refinement"]["observed_descendant_order"]) for row in rows],
            [run_id for row in rows for run_id in row["spatial_refinement"]["run_record_ids"]],
        ),
        (
            "minimum_temporal_descendant_order",
            [float(row["temporal_refinement"]["observed_descendant_order"]) for row in rows],
            [run_id for row in rows for run_id in row["temporal_refinement"]["run_record_ids"]],
        ),
        (
            "minimum_energy_error_order",
            [float(row["energy_behavior"]["observed_maximum_error_order"]) for row in rows],
            [run_id for row in rows for run_id in row["temporal_refinement"]["run_record_ids"]],
        ),
    )
    entries = []
    for threshold_id, values, source_ids in specs:
        measured = min(values)
        candidate = min(1.5, floor_to_half(measured - 0.25))
        entries.append(
            {
                "threshold_id": threshold_id,
                "pilot_source_run_ids": source_ids,
                "measured_pilot_minimum_order": measured,
                "generation_formula": "min(expected_second_order_minus_0.5, floor_to_half(measured_minimum_order_minus_0.25))",
                "rounding_rule": "reserve a quarter-order empirical margin, round downward to a half order, and cap at the preregistered 1.5 second-order acceptance floor",
                "candidate_frozen_threshold": candidate,
                "comparison": "observed order must be strictly greater than the candidate threshold",
                "failure_classification": "NUMERICALLY_BLOCKED:CONVERGENCE_NOT_RESOLVED",
            }
        )
    return entries


def _token(value: float) -> str:
    if value in SOLVER_TOLERANCES:
        return f"{value:.0e}".replace("-", "M").replace("+", "P")
    return str(value).replace("-", "M").replace(".", "P")


def make_record(
    run_id: str,
    scientific_row_id: str,
    run_role: str,
    model_class: str,
    grid_size: int | None,
    time_step: float | None,
    duration: float,
    solver_tolerance: float | None,
    maximum_iterations: int | None,
    initial_condition_identity: str,
    expected_diagnostic: str,
    execution_kind: str = "SIMULATION",
    requested_axis_values: dict[str, Any] | None = None,
    parent_scientific_row_id: str | None = None,
) -> dict[str, Any]:
    output_filename = run_id.replace(":", "__") + ".json"
    return {
        "run_id": run_id,
        "scientific_row_id": scientific_row_id,
        "run_role": run_role,
        "execution_kind": execution_kind,
        "model_or_comparator_class": model_class,
        "grid_size": grid_size,
        "time_step": time_step,
        "duration": duration,
        "solver_tolerance": solver_tolerance,
        "iteration_cap": maximum_iterations,
        "initial_condition_identity": initial_condition_identity,
        "requested_axis_values": requested_axis_values,
        "parent_scientific_row_id": parent_scientific_row_id,
        "expected_diagnostic": expected_diagnostic,
        "output_path": f"{OUTPUT_ROOT}/{output_filename}",
    }


def build_run_matrix(
    guardrail: dict[str, Any], pilot_packet: dict[str, Any]
) -> dict[str, Any]:
    records: list[dict[str, Any]] = []
    rows = guardrail["scientific_matrix"]
    for row in rows:
        row_id = row["row_id"]
        axes = row["requested_axis_values"]
        initial_id = f"GUARDRAIL_v1:{row_id}"
        records.append(
            make_record(
                f"{row_id}:PRIMARY_FULL",
                row_id,
                "PRIMARY_FULL_MODEL",
                "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM",
                PRIMARY_PARAMETERS["grid_size"],
                PRIMARY_PARAMETERS["time_step"],
                PRIMARY_PARAMETERS["duration"],
                PRIMARY_PARAMETERS["solver_tolerance"],
                PRIMARY_PARAMETERS["maximum_iterations"],
                initial_id,
                "evaluate every frozen numerical, model-domain, robustness, and materiality observable without interpretation-driven rerun",
                requested_axis_values=axes,
            )
        )
        for n in GRID_SEQUENCE:
            dt = 0.1 / n
            records.append(
                make_record(
                    f"{row_id}:SPATIAL_N{n}", row_id, "SPATIAL_REFINEMENT", "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM",
                    n, dt, 0.05, 1e-12, 80, initial_id,
                    "included in the fixed three-level spatial descendant convergence fit; exclusion forbidden",
                    requested_axis_values=axes,
                )
            )
        for dt in TEMPORAL_DT_SEQUENCE:
            records.append(
                make_record(
                    f"{row_id}:TEMPORAL_DT{_token(dt)}", row_id, "TEMPORAL_REFINEMENT", "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM",
                    16, dt, 0.05, 1e-12, 80, initial_id,
                    "included in fixed temporal-descendant and energy-error convergence fits; exclusion forbidden",
                    requested_axis_values=axes,
                )
            )
        for tolerance in SOLVER_TOLERANCES:
            records.append(
                make_record(
                    f"{row_id}:SOLVER_TOL{_token(tolerance)}", row_id, "SOLVER_VERIFICATION", "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM",
                    16, 0.003125, 0.05, tolerance, 80, initial_id,
                    "solver contamination and solver-to-truncation hierarchy evaluated without tolerance substitution",
                    requested_axis_values=axes,
                )
            )
        for duplicate in ("A", "B"):
            records.append(
                make_record(
                    f"{row_id}:DETERMINISTIC_{duplicate}", row_id, "DETERMINISTIC_DUPLICATE", "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM",
                    32, 0.0015625, 0.05, 1e-12, 80, initial_id,
                    f"registered numerical payload byte-identical to duplicate {'B' if duplicate == 'A' else 'A'}",
                    requested_axis_values=axes,
                )
            )
        records.append(
            make_record(
                f"{row_id}:FORCED_COMPARATOR", row_id, "FORCED_COMPARATOR", "INTENTIONALLY_NONINVARIANT_COMPARATOR",
                32, 0.0015625, 0.05, 1e-12, 80, f"{initial_id}:DESCENDANTS_REMOVED_AFTER_PARENT_CONSTRUCTION",
                "transverse-equation source residual resolved; negative necessity evidence only; never positive robustness evidence",
                requested_axis_values=axes,
                parent_scientific_row_id=row_id,
            )
        )

    positive_rows = {
        "P_CANONICAL_ACCEPTED_RESULT_UNCHANGED": ("R00_CANONICAL", "SIMULATION"),
        "P_CHARGE_CONJUGATE_PARAMETER_CASE": ("R00_CANONICAL", "ANALYTIC_AND_NUMERICAL_CHECK"),
        "P_ANALYTIC_INVARIANT_DESCENDANT_FREE": ("GLOBAL_CONTROL", "ELIGIBILITY_CHECK"),
        "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED": ("R03_F_ZERO", "SIMULATION"),
        "P_INDEPENDENT_PHI2_EXCITATION": ("R11_CORNER_WEAK_HIGH", "SIMULATION"),
        "P_INDEPENDENT_PHI3_EXCITATION": ("R10_MU_HIGH", "SIMULATION"),
        "P_PHI2_PHI3_INTERCHANGE": ("GLOBAL_CONTROL", "ANALYTIC_CHECK"),
        "P_WEAK_COUPLING_APPROACH": ("R01_ETA_WEAK", "SIMULATION"),
    }
    guardrail_rows = {row["row_id"]: row for row in rows}
    for control in guardrail["positive_controls"]:
        control_id = control["control_id"]
        row_id, kind = positive_rows[control_id]
        numeric = kind in {"SIMULATION", "ANALYTIC_AND_NUMERICAL_CHECK"}
        axes = guardrail_rows[row_id]["requested_axis_values"] if row_id in guardrail_rows else None
        expected = control["expected"]
        if control_id == "P_ANALYTIC_INVARIANT_DESCENDANT_FREE":
            expected = "CONDITIONAL_NOT_EXECUTED_WITHOUT_SEPARATE_ACCEPTED_INVARIANT_SUBDOMAIN_PROOF"
        records.append(
            make_record(
                f"CONTROL_POSITIVE:{control_id}", row_id, "POSITIVE_CONTROL", "POSITIVE_CONTROL_FIXTURE",
                32 if numeric else None, 0.0015625 if numeric else None, 0.05 if numeric else 0.0,
                1e-12 if numeric else None, 80 if numeric else None, f"CONTROL_v1:{control_id}", expected,
                execution_kind=kind, requested_axis_values=axes,
            )
        )

    pilot_negatives = {item["control_id"]: item for item in pilot_packet["summary"]["negative_controls"]}
    dynamic_negative_ids = {
        "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE", "N_DROP_ONLY_PHI2", "N_DROP_ONLY_PHI3",
        "N_OMIT_DESCENDANT_ENERGY", "N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL", "N_REVERSE_TRANSVERSE_EXCHANGE_SIGN",
        "N_WRONG_GAMMA2_BLOCK", "N_WRONG_GAMMA3_BLOCK", "N_SUPPRESS_SECTOR_MULTIPLICITY",
    }
    for control in guardrail["negative_controls"]:
        control_id = control["control_id"]
        dynamic = control_id in dynamic_negative_ids
        records.append(
            make_record(
                f"CONTROL_NEGATIVE:{control_id}", "R00_CANONICAL", "NEGATIVE_CONTROL",
                "DELIBERATELY_CORRUPTED_NEGATIVE_CONTROL" if dynamic else "STATIC_GUARDRAIL_MUTATION",
                16 if dynamic else None, 0.003125 if dynamic else None, 0.05 if dynamic else 0.0,
                1e-12 if dynamic else None, 80 if dynamic else None, f"MUTATION_v1:{control_id}",
                f"reject with only {pilot_negatives[control_id]['expected_diagnostic']}",
                execution_kind="MUTATION_SIMULATION" if dynamic else "STATIC_MUTATION_CHECK",
                requested_axis_values=guardrail_rows["R00_CANONICAL"]["requested_axis_values"],
                parent_scientific_row_id="R00_CANONICAL",
            )
        )

    run_ids = [record["run_id"] for record in records]
    role_counts = dict(sorted(Counter(record["run_role"] for record in records).items()))
    return {
        "schema_id": RUN_MATRIX_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generation_policy": "literal uniform thirteen-role expansion of all fourteen accepted scientific rows plus the exact accepted eight-positive and thirteen-negative control inventories; no filesystem discovery",
        "scientific_row_count": len(rows),
        "scientific_records_per_row": 13,
        "scientific_record_count": 13 * len(rows),
        "control_record_count": 21,
        "invariant_descendant_free_comparator_record_count": 0,
        "invariant_descendant_free_comparator_reason": guardrail["comparator_policy"]["descendant_free_special_subdomain"],
        "record_count": len(records),
        "unique_run_id_count": len(set(run_ids)),
        "role_counts": role_counts,
        "records": records,
    }


def environment_identity() -> dict[str, Any]:
    paths = ["requirements.active.lock", "formal/toe_formal/lean-toolchain", "formal/toe_formal/lake-manifest.json", ".gitattributes"]
    return {
        "python_version": platform.python_version(),
        "operating_system": platform.system(),
        "os_release": platform.release(),
        "canonical_serialization": "sorted-key UTF-8 NFC JSON with LF and finite numbers only",
        "required_process_environment": {"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"},
        "bound_files": [{"path": path, "sha256": sha256_path(REPO_ROOT / path)} for path in paths],
    }


DECISION_IDS = [
    "accepted_pilot_review_is_exact_live_authority",
    "accepted_guardrail_pilot_and_independent_review_artifacts_are_hash_bound",
    "all_fourteen_scientific_rows_are_immutable_and_uniformly_expanded",
    "two_hundred_three_role_qualified_records_are_literal_complete_and_unique",
    "primary_spatial_temporal_solver_duplicate_and_forced_roles_exist_for_every_row",
    "eight_positive_and_thirteen_negative_control_records_are_exact",
    "no_invariant_descendant_free_comparator_is_invented_without_accepted_proof",
    "twenty_two_residual_and_floor_thresholds_reconstruct_mechanically_from_registered_pilot_arrays",
    "three_convergence_thresholds_are_mechanically_generated_with_fixed_fit_members",
    "solver_ratio_iteration_axis_and_determinism_gates_are_frozen",
    "scientific_materiality_gates_and_sensitivity_values_are_unchanged",
    "forced_comparators_preserve_parent_provenance_and_remain_negative_only",
    "robustness_and_descendant_significance_outcomes_remain_separate",
    "custody_controls_numerical_admissibility_domain_robustness_necessity_materiality_and_claim_order_is_deterministic",
    "no_row_exclusion_threshold_relaxation_fit_change_or_interpretation_rerun_is_allowed",
    "classifier_implementation_must_be_committed_and_hash_bound_before_evaluation",
    "pre_correction_classifier_source_blob_limitation_is_permanently_preserved",
    "preparation_selects_only_independent_freeze_review",
    "canonical_execution_and_all_new_scientific_claims_remain_unauthorized_before_review",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    validate_authority()
    guardrail = load_json(REPO_ROOT / GUARDRAIL_PACKET_RELATIVE_PATH)
    pilot_packet = load_json(REPO_ROOT / PILOT_PACKET_RELATIVE_PATH)
    pilot_arrays = load_json(REPO_ROOT / PILOT_ARRAYS_RELATIVE_PATH)
    pilot_review = load_json(REPO_ROOT / PILOT_REVIEW_REPORT_RELATIVE_PATH)
    row_ids = [row["row_id"] for row in guardrail["scientific_matrix"]]
    run_matrix = build_run_matrix(guardrail, pilot_packet)
    run_matrix_sha256 = sha256_bytes(canonical_json_bytes(run_matrix))
    thresholds = threshold_provenance(pilot_packet, pilot_arrays, row_ids)
    convergence = convergence_thresholds(pilot_packet)
    classification = guardrail["result_classification_freeze"]
    materiality = guardrail["threshold_freeze"]

    packet = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "authority_basis": {
            "pilot_review_commit": PILOT_REVIEW_COMMIT,
            "pilot_review_parent": PILOT_REVIEW_PARENT,
            "pilot_review_verdict": pilot_review["verdict"],
            "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        },
        "scientific_design_freeze": {
            "scientific_row_ids": row_ids,
            "scientific_rows": [
                {"row_id": row["row_id"], "row_role": row["row_role"], "requested_axis_values": row["requested_axis_values"]}
                for row in guardrail["scientific_matrix"]
            ],
            "row_count": 14,
            "axis_levels_changed": False,
            "observable_definitions_changed": False,
            "control_inventory_changed": False,
            "materiality_definitions_changed": False,
        },
        "proposed_numerical_parameter_freeze": {
            "primary_full_model": PRIMARY_PARAMETERS,
            "spatial_refinement": {"grid_sequence": GRID_SEQUENCE, "time_step_rule": "dt=0.1/N", "duration": 0.05, "solver_tolerance": 1e-12, "maximum_iterations": 80},
            "temporal_refinement": {"grid_size": 16, "time_step_sequence": TEMPORAL_DT_SEQUENCE, "duration": 0.05, "solver_tolerance": 1e-12, "maximum_iterations": 80},
            "solver_verification": {"grid_size": 16, "time_step": 0.003125, "duration": 0.05, "solver_tolerance_sequence": SOLVER_TOLERANCES, "maximum_iterations": 80},
            "selection_rule": "uniform across all fourteen rows; primary uses the finest accepted pilot grid, finest accepted pilot timestep, tightest accepted pilot tolerance, accepted duration, and accepted cap",
            "primary_is_declared_cross_product_not_a_claim_that_exact_tuple_was_piloted": True,
            "row_specific_rescue_parameters_forbidden": True,
        },
        "canonical_run_matrix": {"path": RUN_MATRIX_RELATIVE_PATH, "sha256": run_matrix_sha256, "record_count": run_matrix["record_count"]},
        "execution_consumer_contract": {
            "required_run_matrix_path": RUN_MATRIX_RELATIVE_PATH,
            "required_run_matrix_sha256": run_matrix_sha256,
            "required_record_count": 203,
            "unknown_missing_or_duplicate_record_behavior": "refuse execution and preserve the custody failure",
            "dynamic_run_discovery_or_generation": "forbidden",
            "execution_order_source": "the exact record order in the hash-bound matrix",
            "output_overwrite": "forbidden; role-qualified outputs are immutable",
            "interpretation_driven_rerun": "forbidden",
        },
        "numerical_threshold_provenance": thresholds,
        "convergence_threshold_provenance": convergence,
        "fixed_structural_numerical_gates": {
            "maximum_solver_to_truncation_ratio": 0.01,
            "maximum_iterations": 80,
            "axis_round_trip_absolute_tolerance": 2e-15,
            "loading_upper_admissibility_ceiling": 0.8,
            "all_registered_values_finite": True,
            "all_required_steps_converged": True,
            "deterministic_duplicate_rule": "byte-identical registered numerical payloads under the bound environment",
            "fit_members_may_be_excluded": False,
            "fit_ranges_may_change_after_execution": False,
        },
        "scientific_materiality_freeze": {
            "material_R_perp_gate": materiality["material_R_perp_gate"],
            "material_F_exchange_perp_gate": materiality["material_F_exchange_perp_gate"],
            "descendant_dominated_R_perp_gate": materiality["descendant_dominated_R_perp_gate"],
            "descendant_dominated_F_exchange_perp_gate": materiality["descendant_dominated_F_exchange_perp_gate"],
            "threshold_sensitivity_values": materiality["threshold_sensitivity_values"],
            "resolved_above_floor_rule": materiality["resolved_above_numerical_floor_rule"],
            "delta_O_for_T_DIVERGENCE": materiality["delta_O_for_T_DIVERGENCE"],
            "source": "accepted guardrail v1; unchanged by pilot or calibration",
        },
        "comparator_freeze": {
            "full_model_class": guardrail["comparator_policy"]["full_model_id"],
            "forced_comparator_class": guardrail["comparator_policy"]["forced_comparator_id"],
            "forced_comparator_positive_robustness_eligible": False,
            "forced_comparator_negative_necessity_only": True,
            "parent_requested_axis_values_and_loading_preserved": True,
            "realized_loading_after_forced_removal": "NOT_PHYSICALLY_ELIGIBLE",
            "invariant_descendant_free_comparator": "NOT_REGISTERED_WITHOUT_SEPARATE_ACCEPTED_INVARIANCE_PROOF",
        },
        "observable_and_energy_freeze": {
            "observable_inventory": guardrail["observable_freeze"]["inventory"],
            "measurement_contract": guardrail["observable_freeze"]["measurement_contract"],
            "energy_class": "BOUNDED_CONVERGENT_ENERGY_ERROR",
            "drift_shape_recorded_but_not_used_as_automatic_instability": True,
            "energy_acceptance": "bounded over duration, finest error no larger than coarsest, and frozen three-level order threshold passed",
            "signed_total_energy_role": "physical conservation and exchange diagnostic only",
            "positive_loading_role": "initial-state design coordinate only",
        },
        "deterministic_outcome_logic": {
            "evaluation_order": [
                "verify custody and complete run matrix",
                "verify positive and negative controls",
                "verify numerical evidence availability and admissibility for every full-model row",
                "apply model-domain criteria without dropping rows",
                "classify robustness across all admitted rows",
                "evaluate forced-comparator necessity evidence",
                "classify descendant significance separately",
                "apply sensitivity analysis and bounded claim ceiling",
            ],
            "preclassification_blocks": {
                "custody_failure": "NO_SCIENTIFIC_CLASSIFICATION; B-BLOCKED_CUSTODY",
                "control_failure": "NO_SCIENTIFIC_CLASSIFICATION; B-BLOCKED_CONTROL_DISCRIMINATION",
            },
            "robustness_classification_order": classification["classification_order"],
            "robustness_decision_rules": classification["robustness_decision_rules"],
            "descendant_significance_decision_rules": classification["descendant_significance_decision_rules"],
            "descendant_significance_classes": [item["outcome_id"] for item in classification["descendant_significance_classes"]],
            "separation_rule": "robustness status and descendant-significance status are independent fields; neither overwrites the other",
            "controlled_row_failure_rule": "a row with complete classifiable evidence may fail a frozen robustness threshold and contribute to CONDITIONAL_ROBUST; a row lacking classifiable evidence contributes to NUMERICALLY_BLOCKED",
            "no_significance_when_blocked_or_model_domain_limited": True,
        },
        "classifier_versioning_and_provenance": {
            "decision_rule_bundle_id": "DM_ROBUSTNESS_DECISION_RULE_BUNDLE_v1",
            "decision_rule_specification_is_this_hash_bound_packet": True,
            "classifier_implementation": {"path": CLASSIFIER_RELATIVE_PATH, "sha256": CLASSIFIER_SHA256},
            "classifier_implementation_present_in_freeze_proposal": True,
            "classifier_implementation_must_be_committed_before_first_evaluation": True,
            "classifier_source_path_and_sha256_must_be_bound_by_independent_freeze_review": True,
            "execution_must_refuse_uncommitted_or_hash_mismatched_classifier": True,
            "classifier_change_after_any_output_requires_new_versioned_freeze_and_independent_review": True,
            "pre_correction_source_blob_bound": False,
            "permanent_limitation": pilot_review["classifier_repair_audit"]["pre_correction_traceability_limitation"],
            "permanent_process_rule": "every future classifier or decision-rule implementation must be committed and hash-bound before it evaluates scientific output",
        },
        "failure_and_rerun_semantics": {
            "failed_or_difficult_rows_remain_in_evidence": True,
            "row_drop": "forbidden",
            "threshold_relaxation": "forbidden; preserve the result and rotate to a versioned repair review",
            "grid_or_timestep_change_after_execution": "forbidden",
            "fit_range_change_after_execution": "forbidden",
            "interaction_corner_reclassification": "forbidden",
            "materiality_change": "forbidden",
            "interpretation_driven_rerun": "forbidden",
            "rerun_allowed_only_for": "byte-identical reproduction under the same frozen identity, or a separately authorized versioned repair that cannot overwrite v1 evidence",
        },
        "environment_identity": environment_identity(),
        "lean_status_boundary": {
            "affected_preparation_authority_build": {"status": "PASSED", "job_count": 142},
            "historical_repository_wide_aggregate": {"completed_jobs": 8441, "total_jobs": 8507, "termination": "TIMEOUT_AT_600_SECONDS", "theorem_error_observed_before_timeout": False, "status": "INCOMPLETE"},
            "repository_wide_green_claim": False,
        },
        "selected_next_target": REVIEW_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "blocked_target": BLOCKED_TARGET,
        "authority_boundary": {
            "packet_prepared": True,
            "packet_independently_accepted": False,
            "numerical_parameters_authoritatively_frozen": False,
            "numerical_thresholds_authoritatively_frozen": False,
            "canonical_fourteen_row_execution_authorized": False,
            "robustness_classification_assigned": False,
            "descendant_significance_assigned": False,
            "new_E_REPRO_claim": False,
            "previous_canonical_E_REPRO_unchanged": True,
        },
        "claim_ceiling": "A complete calibration and fourteen-row execution-freeze proposal is prepared for independent review. It does not authorize execution or assign robustness, descendant significance, or a new E-REPRO claim.",
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256},
        "nonclaims": [
            "no canonical fourteen-row run executed", "no robustness classification", "no descendant-materiality classification",
            "no new E-REPRO result", "no empirical validation", "no pillar completion", "no seam closure",
            "no C_k dynamics", "no CCFT promotion", "no master-action promotion", "no repository-wide green claim",
        ],
    }
    packet_raw = canonical_json_bytes(packet)
    matrix_raw = canonical_json_bytes(run_matrix)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "classifier": {"path": CLASSIFIER_RELATIVE_PATH, "sha256": CLASSIFIER_SHA256},
        "inputs": packet["authority_basis"]["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "run_matrix": {"path": RUN_MATRIX_RELATIVE_PATH, "sha256": sha256_bytes(matrix_raw)},
        "environment": packet["environment_identity"],
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    expected_roles = {
        "DETERMINISTIC_DUPLICATE": 28,
        "FORCED_COMPARATOR": 14,
        "NEGATIVE_CONTROL": 13,
        "POSITIVE_CONTROL": 8,
        "PRIMARY_FULL_MODEL": 14,
        "SOLVER_VERIFICATION": 42,
        "SPATIAL_REFINEMENT": 42,
        "TEMPORAL_REFINEMENT": 42,
    }
    prepared = (
        len(row_ids) == len(set(row_ids)) == 14
        and run_matrix["record_count"] == run_matrix["unique_run_id_count"] == 203
        and run_matrix["role_counts"] == expected_roles
        and len(thresholds) == 22
        and all(item["candidate_frozen_threshold"] == item["recomputed_threshold"] for item in thresholds)
        and len(convergence) == 3
        and all(item["candidate_frozen_threshold"] == 1.5 for item in convergence)
        and packet["scientific_materiality_freeze"]["material_R_perp_gate"] == 0.1
        and packet["scientific_materiality_freeze"]["descendant_dominated_R_perp_gate"] == 0.5
    )
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW" if prepared else "B-BLOCKED",
        "selected_next_target": REVIEW_TARGET if prepared else BLOCKED_TARGET,
        "all_decisions_passed": prepared,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": prepared} for item in DECISION_IDS],
        "scientific_row_count": len(row_ids),
        "run_record_count": run_matrix["record_count"],
        "role_counts": run_matrix["role_counts"],
        "mechanically_reconstructed_residual_and_floor_threshold_count": len(thresholds),
        "mechanically_generated_convergence_threshold_count": len(convergence),
        "proposed_primary_parameters": PRIMARY_PARAMETERS,
        "artifact_hashes": {
            "generator_sha256": sha256_path(SCRIPT_PATH),
            "classifier_sha256": CLASSIFIER_SHA256,
            "packet_sha256": sha256_bytes(packet_raw),
            "run_matrix_sha256": sha256_bytes(matrix_raw),
            "manifest_sha256": sha256_bytes(manifest_raw),
        },
        "authority_boundary": packet["authority_boundary"],
        "claim": packet["claim_ceiling"],
        "nonclaims": packet["nonclaims"],
    }
    return packet, run_matrix, manifest, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the descendant-necessity robustness calibration and full-run freeze packet v1.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, matrix, manifest, report = build_artifacts()
    except (OSError, ValueError, KeyError, StopIteration, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = ((PACKET_PATH, packet), (RUN_MATRIX_PATH, matrix), (MANIFEST_PATH, manifest), (REPORT_PATH, report))
    if args.write:
        for path, payload in artifacts:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(canonical_json_bytes(payload))
        print(f"wrote robustness calibration/freeze proposal: {report['verdict']}; independent review required")
        return 0 if report["all_decisions_passed"] else 2
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing calibration/freeze artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(f"robustness calibration/freeze proposal verified: {report['verdict']}; canonical execution unauthorized")
        return 0 if report["all_decisions_passed"] else 2
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0 if report["all_decisions_passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
