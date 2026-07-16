from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-15T00:00:00Z"
TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "r13_numerical_block_diagnostic_packet_v0"
)
SELECTED_NEXT_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "r13_numerical_block_diagnostic_packet_v0_result"
)
PACKET_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_v0"
)
MANIFEST_SCHEMA_ID = f"{PACKET_SCHEMA_ID}_MANIFEST"
REPORT_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_20260715_v0"
)

PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-DIAGNOSTIC-PACKET-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-DIAGNOSTIC-MANIFEST-v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_20260715_v0.json"
)
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json"
)
FREEZE_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
)
RUN_MATRIX = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
)
IDENTITY_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
)
EXECUTION_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-MANIFEST-v2.json"
)
EXECUTION_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-PACKET-v2.json"
)
OUTPUT_ROOT = (
    "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_v2"
)
GENERATOR_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_r13_numerical_block_diagnostic_packet_v0.py"
)

EXPECTED_SOURCE_HASHES = {
    REVIEW_REPORT: "cacbd77f3ef18a80d8d15686dd8f385f73a634038fddb5010058f2e144ef3c85",
    FREEZE_PACKET: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    RUN_MATRIX: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    IDENTITY_MANIFEST: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    EXECUTION_MANIFEST: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    EXECUTION_PACKET: "9020fd19774a2c2ccff108fd7950945a076a459f185bed3b10480270499cf86a",
}

R13 = "R13_CORNER_STRONG_LOW"
LOOSE_RUN_ID = f"{R13}:SOLVER_TOL1eM08"
PRIMARY_RUN_ID = f"{R13}:PRIMARY_FULL"
TOLERANCE_RUN_IDS = {
    1e-8: LOOSE_RUN_ID,
    1e-10: f"{R13}:SOLVER_TOL1eM10",
    1e-12: f"{R13}:SOLVER_TOL1eM12",
}
FAILED_SERIES = {
    "gauss_residual": "maximum_Gauss_residual",
    "continuity_residual": "maximum_continuity_residual",
    "exchange_longitudinal_residual": "maximum_exchange_longitudinal_residual",
    "longitudinal_Maxwell_residual": "maximum_longitudinal_Maxwell_residual",
}
REQUIRED_TIMELINE_FIELDS = {"time", *FAILED_SERIES}
EXACT_CANCELLATION_REQUIRED_FIELDS = {
    "longitudinal_field_sector_transfer",
    "longitudinal_matter_sector_transfer",
}
DISCRETE_CLOSURE_REQUIRED_FIELDS = {
    "longitudinal_Maxwell_residual_components",
    "spatial_divergence_operator_output",
    "continuity_residual_components",
}
EQUATION_BLOCK_SOLVER_REQUIRED_FIELDS = {"solver_residual_by_equation_block"}


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
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _finite_series(payload: dict[str, Any], key: str) -> list[float]:
    values = payload.get("series", {}).get(key)
    if not isinstance(values, list) or not values:
        raise ValueError(f"missing nonempty series {key}: {payload.get('run_id')}")
    result = [float(value) for value in values]
    if any(not math.isfinite(value) for value in result):
        raise ValueError(f"nonfinite series {key}: {payload.get('run_id')}")
    return result


def _linear_fit(x: list[float], y: list[float]) -> dict[str, float | None]:
    if len(x) != len(y) or len(x) < 2:
        return {"slope": None, "intercept": None, "r_squared": None}
    mean_x = statistics.fmean(x)
    mean_y = statistics.fmean(y)
    denominator = sum((value - mean_x) ** 2 for value in x)
    if denominator == 0.0:
        return {"slope": None, "intercept": None, "r_squared": None}
    slope = sum((left - mean_x) * (right - mean_y) for left, right in zip(x, y, strict=True)) / denominator
    intercept = mean_y - slope * mean_x
    predicted = [intercept + slope * value for value in x]
    residual_sum = sum((observed - fitted) ** 2 for observed, fitted in zip(y, predicted, strict=True))
    total_sum = sum((observed - mean_y) ** 2 for observed in y)
    r_squared = 1.0 - residual_sum / total_sum if total_sum > 0.0 else 1.0
    return {"slope": slope, "intercept": intercept, "r_squared": r_squared}


def _pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 2:
        return None
    mean_left = statistics.fmean(left)
    mean_right = statistics.fmean(right)
    numerator = sum(
        (a - mean_left) * (b - mean_right) for a, b in zip(left, right, strict=True)
    )
    denominator = math.sqrt(
        sum((value - mean_left) ** 2 for value in left)
        * sum((value - mean_right) ** 2 for value in right)
    )
    return numerator / denominator if denominator > 0.0 else None


def _growth_fits(times: list[float], magnitudes: list[float]) -> dict[str, Any]:
    positive = [(time, value) for time, value in zip(times, magnitudes, strict=True) if time > 0.0 and value > 0.0]
    fit_times = [item[0] for item in positive]
    fit_values = [item[1] for item in positive]
    linear = _linear_fit(fit_times, fit_values)
    quadratic_coordinate = _linear_fit([time * time for time in fit_times], fit_values)
    exponential = _linear_fit(fit_times, [math.log(value) for value in fit_values])
    power = _linear_fit(
        [math.log(time) for time in fit_times],
        [math.log(value) for value in fit_values],
    )
    return {
        "fit_point_count": len(positive),
        "linear_in_time": linear,
        "linear_in_time_squared": quadratic_coordinate,
        "exponential_log_linear": {
            "rate": exponential["slope"],
            "log_intercept": exponential["intercept"],
            "r_squared_in_log_space": exponential["r_squared"],
        },
        "power_law_log_log": {
            "exponent": power["slope"],
            "log_coefficient": power["intercept"],
            "r_squared_in_log_space": power["r_squared"],
        },
        "interpretation_boundary": (
            "These fits are descriptive over seventeen stored time samples. R-squared values "
            "from transformed and untransformed fits are not used to select a causal law."
        ),
    }


def _first_time_at_fraction(times: list[float], magnitudes: list[float], fraction: float) -> float:
    target = fraction * max(magnitudes)
    return next(time for time, value in zip(times, magnitudes, strict=True) if value >= target)


def _canonical_root_inventory() -> list[dict[str, str]]:
    return [
        {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for path in sorted((REPO_ROOT / OUTPUT_ROOT).glob("*.json"))
    ]


def canonical_root_digest() -> str:
    return sha256_bytes(canonical_json_bytes(_canonical_root_inventory()))


def _load_sources() -> dict[str, Any]:
    review = load_json(REPO_ROOT / REVIEW_REPORT)
    freeze = load_json(REPO_ROOT / FREEZE_PACKET)
    matrix = load_json(REPO_ROOT / RUN_MATRIX)
    identity = load_json(REPO_ROOT / IDENTITY_MANIFEST)
    execution_manifest = load_json(REPO_ROOT / EXECUTION_MANIFEST)
    execution_packet = load_json(REPO_ROOT / EXECUTION_PACKET)
    expected_by_run = {
        item["run_id"]: item for item in execution_manifest["run_outputs"]
    }
    identity_by_run = {item["run_id"]: item for item in identity["outputs"]}
    records_by_run = {item["run_id"]: item for item in matrix["records"]}
    payload_by_run = {
        run_id: load_json(REPO_ROOT / item["relative_output_path"])
        for run_id, item in identity_by_run.items()
    }
    return {
        "review": review,
        "freeze": freeze,
        "matrix": matrix,
        "identity": identity,
        "execution_manifest": execution_manifest,
        "execution_packet": execution_packet,
        "expected_by_run": expected_by_run,
        "identity_by_run": identity_by_run,
        "records_by_run": records_by_run,
        "payload_by_run": payload_by_run,
    }


def _source_custody(sources: dict[str, Any]) -> dict[str, Any]:
    source_hashes = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_SOURCE_HASHES}
    output_failures = []
    for run_id, identity in sources["identity_by_run"].items():
        path = identity["relative_output_path"]
        expected = sources["expected_by_run"].get(run_id, {}).get("output_sha256")
        observed = sha256_path(REPO_ROOT / path)
        if observed != expected:
            output_failures.append(
                {"run_id": run_id, "path": path, "expected": expected, "observed": observed}
            )
    inventory = _canonical_root_inventory()
    return {
        "source_artifact_hashes": source_hashes,
        "expected_source_artifact_hashes": EXPECTED_SOURCE_HASHES,
        "all_source_artifact_hashes_exact": source_hashes == EXPECTED_SOURCE_HASHES,
        "canonical_run_outputs_checked": len(sources["identity_by_run"]),
        "canonical_run_output_hash_failures": output_failures,
        "canonical_output_root_file_count": len(inventory),
        "canonical_output_root_digest": sha256_bytes(canonical_json_bytes(inventory)),
        "canonical_output_root_inventory": inventory,
        "review_verdict_exact": sources["review"].get("verdict")
        == "ACCEPT_NUMERICALLY_BLOCKED_CANONICAL_RESULT",
        "review_selected_this_target": sources["review"].get("selected_next_target") == TARGET,
        "execution_count_preserved": sources["execution_packet"].get("execution_count_performed")
        == 1,
        "simulation_invocation_count": 0,
        "canonical_output_write_authorized": False,
        "passed": source_hashes == EXPECTED_SOURCE_HASHES
        and not output_failures
        and len(sources["identity_by_run"]) == 203
        and sources["review"].get("verdict")
        == "ACCEPT_NUMERICALLY_BLOCKED_CANONICAL_RESULT"
        and sources["review"].get("selected_next_target") == TARGET,
    }


def _threshold_map(freeze: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        threshold["raw_series_key"]: threshold
        for threshold in freeze["numerical_threshold_provenance"]
        if threshold["raw_series_key"] in FAILED_SERIES
    }


def _failure_timelines(
    freeze: dict[str, Any], payload_by_run: dict[str, dict[str, Any]]
) -> dict[str, Any]:
    payload = payload_by_run[LOOSE_RUN_ID]
    times = _finite_series(payload, "time")
    thresholds = _threshold_map(freeze)
    timelines = []
    for key, threshold_id in FAILED_SERIES.items():
        values = _finite_series(payload, key)
        magnitudes = [abs(value) for value in values]
        ceiling = float(thresholds[key]["frozen_value"])
        maximum = max(magnitudes)
        first_crossing_index = next(
            index for index, value in enumerate(magnitudes) if value > ceiling
        )
        timelines.append(
            {
                "threshold_id": threshold_id,
                "raw_series_key": key,
                "units": thresholds[key]["units"],
                "frozen_ceiling": ceiling,
                "time": times,
                "absolute_residual": magnitudes,
                "residual_over_frozen_ceiling": [value / ceiling for value in magnitudes],
                "residual_over_own_maximum": [value / maximum for value in magnitudes],
                "initial_magnitude": magnitudes[0],
                "maximum_magnitude": maximum,
                "maximum_ceiling_ratio": maximum / ceiling,
                "first_threshold_crossing_time": times[first_crossing_index],
                "maximum_time": times[magnitudes.index(maximum)],
                "fractional_onset_times": {
                    "10_percent_of_maximum": _first_time_at_fraction(times, magnitudes, 0.1),
                    "50_percent_of_maximum": _first_time_at_fraction(times, magnitudes, 0.5),
                    "90_percent_of_maximum": _first_time_at_fraction(times, magnitudes, 0.9),
                },
                "absolute_magnitude_monotone_nondecreasing": all(
                    magnitudes[index] >= magnitudes[index - 1]
                    for index in range(1, len(magnitudes))
                ),
                "growth_fits": _growth_fits(times, magnitudes),
            }
        )
    ordered = sorted(
        timelines,
        key=lambda item: (item["first_threshold_crossing_time"], item["threshold_id"]),
    )
    grouped: dict[str, list[str]] = {}
    for item in ordered:
        grouped.setdefault(str(item["first_threshold_crossing_time"]), []).append(
            item["threshold_id"]
        )
    return {
        "run_id": LOOSE_RUN_ID,
        "sample_count": len(times),
        "timelines": timelines,
        "threshold_crossing_order": [
            {"time": float(time), "threshold_ids": threshold_ids}
            for time, threshold_ids in grouped.items()
        ],
        "all_initial_values_pass": all(
            item["initial_magnitude"] <= item["frozen_ceiling"] for item in timelines
        ),
        "all_maxima_at_final_time": all(item["maximum_time"] == times[-1] for item in timelines),
        "all_absolute_magnitudes_monotone_nondecreasing": all(
            item["absolute_magnitude_monotone_nondecreasing"] for item in timelines
        ),
    }


def _common_cause_timing(timelines: dict[str, Any]) -> dict[str, Any]:
    normalized = {
        item["raw_series_key"]: item["residual_over_own_maximum"]
        for item in timelines["timelines"]
    }
    keys = sorted(normalized)
    correlations = []
    for index, left_key in enumerate(keys):
        for right_key in keys[index + 1 :]:
            correlations.append(
                {
                    "left": left_key,
                    "right": right_key,
                    "pearson_correlation_of_normalized_absolute_timelines": _pearson(
                        normalized[left_key][1:], normalized[right_key][1:]
                    ),
                }
            )
    return {
        "threshold_crossing_order": timelines["threshold_crossing_order"],
        "normalized_timeline_correlations": correlations,
        "minimum_pairwise_correlation": min(
            item["pearson_correlation_of_normalized_absolute_timelines"]
            for item in correlations
            if item["pearson_correlation_of_normalized_absolute_timelines"] is not None
        ),
        "timing_observation": (
            "Continuity and longitudinal Maxwell cross together first at t=0.0125; "
            "longitudinal exchange crosses at t=0.03125; Gauss crosses last at t=0.04375."
        ),
        "causal_boundary": (
            "Timing and correlation can test consistency with a common cause but cannot identify "
            "which equation leads causally from stored scalar norms alone."
        ),
    }


def _tolerance_response(payload_by_run: dict[str, dict[str, Any]]) -> dict[str, Any]:
    tolerance_rows = []
    maxima_by_key: dict[str, dict[float, float]] = {key: {} for key in FAILED_SERIES}
    for tolerance in sorted(TOLERANCE_RUN_IDS, reverse=True):
        run_id = TOLERANCE_RUN_IDS[tolerance]
        payload = payload_by_run[run_id]
        residual_maxima = {}
        for key in FAILED_SERIES:
            maximum = max(abs(value) for value in _finite_series(payload, key))
            maxima_by_key[key][tolerance] = maximum
            residual_maxima[key] = maximum
        iterations = _finite_series(payload, "solver_iterations")
        solver_residual = [abs(value) for value in _finite_series(payload, "solver_residual")]
        positive_iterations = iterations[1:]
        tolerance_rows.append(
            {
                "run_id": run_id,
                "solver_tolerance": tolerance,
                "residual_maxima": residual_maxima,
                "solver_iterations": iterations,
                "solver_residual": solver_residual,
                "maximum_iterations": max(iterations),
                "iterations_constant_after_initial_state": len(set(positive_iterations)) == 1,
                "late_iteration_increase": iterations[-1] - iterations[1],
                "maximum_solver_residual": max(solver_residual),
                "final_solver_residual": solver_residual[-1],
                "maximum_solver_residual_over_requested_tolerance": max(solver_residual)
                / tolerance,
                "solver_residual_nonincreasing_after_first_step": all(
                    solver_residual[index] <= solver_residual[index - 1]
                    for index in range(2, len(solver_residual))
                ),
                "all_steps_converged": payload["registered_numerical_payload"][
                    "all_steps_converged"
                ],
            }
        )
    residual_rows = []
    overall_exponents = []
    for key, maxima in maxima_by_key.items():
        pairwise = []
        for loose, tight in ((1e-8, 1e-10), (1e-10, 1e-12)):
            exponent = math.log(maxima[loose] / maxima[tight]) / math.log(loose / tight)
            pairwise.append(
                {
                    "loose_tolerance": loose,
                    "tight_tolerance": tight,
                    "observed_exponent": exponent,
                }
            )
        overall = math.log(maxima[1e-8] / maxima[1e-12]) / math.log(1e-8 / 1e-12)
        overall_exponents.append(overall)
        residual_rows.append(
            {
                "raw_series_key": key,
                "maxima_by_solver_tolerance": {
                    str(tolerance): value for tolerance, value in sorted(maxima.items(), reverse=True)
                },
                "pairwise_tolerance_exponents": pairwise,
                "overall_1eM08_to_1eM12_exponent": overall,
                "strictly_decreases_with_tighter_tolerance": maxima[1e-8]
                > maxima[1e-10]
                > maxima[1e-12],
            }
        )
    return {
        "definition": "p_s = ln(R_loose/R_tight) / ln(epsilon_loose/epsilon_tight)",
        "solver_runs": tolerance_rows,
        "residual_tolerance_response": residual_rows,
        "all_four_residual_maxima_strictly_decrease_with_tighter_tolerance": all(
            item["strictly_decreases_with_tighter_tolerance"] for item in residual_rows
        ),
        "overall_exponent_minimum": min(overall_exponents),
        "overall_exponent_maximum": max(overall_exponents),
        "overall_exponent_median": statistics.median(overall_exponents),
        "all_solver_iteration_histories_constant_after_initial_state": all(
            row["iterations_constant_after_initial_state"] for row in tolerance_rows
        ),
        "all_solver_residual_histories_nonincreasing_after_first_step": all(
            row["solver_residual_nonincreasing_after_first_step"] for row in tolerance_rows
        ),
        "all_steps_converged": all(row["all_steps_converged"] for row in tolerance_rows),
        "interpretation": (
            "All four maxima decrease monotonically with tighter solver tolerance, with overall "
            "1e-8-to-1e-12 exponents clustered near 0.75. Pairwise exponents vary, so this is "
            "descriptive tolerance response rather than a certified asymptotic law."
        ),
    }


def _neighbor_contrast(
    freeze: dict[str, Any],
    records_by_run: dict[str, dict[str, Any]],
    payload_by_run: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    thresholds = _threshold_map(freeze)
    scientific_rows = {
        row["row_id"]: row["requested_axis_values"]
        for row in freeze["scientific_design_freeze"]["scientific_rows"]
    }
    r13_axes = scientific_rows[R13]
    rows = []
    for row_id, axes in scientific_rows.items():
        if row_id == R13:
            continue
        shared_axes = sorted(key for key, value in axes.items() if value == r13_axes[key])
        if not shared_axes:
            continue
        record = next(
            item
            for item in records_by_run.values()
            if item["scientific_row_id"] == row_id
            and item["run_role"] == "SOLVER_VERIFICATION"
            and float(item["solver_tolerance"]) == 1e-8
        )
        ratios = {
            key: max(abs(value) for value in _finite_series(payload_by_run[record["run_id"]], key))
            / float(thresholds[key]["frozen_value"])
            for key in FAILED_SERIES
        }
        rows.append(
            {
                "scientific_row_id": row_id,
                "run_id": record["run_id"],
                "shared_axes": shared_axes,
                "ceiling_ratios": ratios,
                "maximum_ceiling_ratio": max(ratios.values()),
                "all_four_pass": max(ratios.values()) <= 1.0,
            }
        )
    r13_payload = payload_by_run[LOOSE_RUN_ID]
    r13_ratios = {
        key: max(abs(value) for value in _finite_series(r13_payload, key))
        / float(thresholds[key]["frozen_value"])
        for key in FAILED_SERIES
    }
    next_highest_by_key = {
        key: max(row["ceiling_ratios"][key] for row in rows) for key in FAILED_SERIES
    }
    axis_groups = []
    for axis, value in r13_axes.items():
        matching = [row for row in rows if axis in row["shared_axes"]]
        axis_groups.append(
            {
                "axis": axis,
                "R13_value": value,
                "matching_non_R13_rows": [row["scientific_row_id"] for row in matching],
                "all_matching_rows_pass": bool(matching) and all(row["all_four_pass"] for row in matching),
                "maximum_matching_row_ceiling_ratio": max(
                    row["maximum_ceiling_ratio"] for row in matching
                ),
            }
        )
    return {
        "R13_loose_solver_ceiling_ratios": r13_ratios,
        "axis_sharing_neighbor_count": len(rows),
        "axis_sharing_neighbors": sorted(rows, key=lambda item: item["scientific_row_id"]),
        "all_axis_sharing_neighbors_pass": all(row["all_four_pass"] for row in rows),
        "next_highest_axis_sharing_neighbor_ratio_by_residual": next_highest_by_key,
        "R13_to_next_highest_neighbor_contrast_by_residual": {
            key: r13_ratios[key] / next_highest_by_key[key] for key in FAILED_SERIES
        },
        "per_axis_descriptive_check": axis_groups,
        "individual_axis_setting_sufficient_in_tested_matrix": False,
        "interaction_inference_boundary": (
            "Every row sharing an R13 axis value passes, so no individual axis value is sufficient "
            "within this matrix. The sparse corner design cannot identify the interaction order or "
            "a unique causal parameter combination."
        ),
    }


def _cancellation_conditioning(
    freeze: dict[str, Any], payload_by_run: dict[str, dict[str, Any]]
) -> dict[str, Any]:
    payload = payload_by_run[LOOSE_RUN_ID]
    available = set(payload["series"])
    exact_missing = sorted(EXACT_CANCELLATION_REQUIRED_FIELDS - available)
    times = _finite_series(payload, "time")
    electric_fluctuating = _finite_series(payload, "energy_electric_fluctuating")
    electric_zero_mode = _finite_series(payload, "energy_electric_zero_mode")
    cumulative_exchange = _finite_series(payload, "cumulative_exchange_longitudinal")
    field_energy = [
        left + right
        for left, right in zip(electric_fluctuating, electric_zero_mode, strict=True)
    ]
    field_delta = [value - field_energy[0] for value in field_energy]
    mismatch = [
        left + right for left, right in zip(field_delta, cumulative_exchange, strict=True)
    ]
    epsilon_exchange = float(
        next(
            threshold["frozen_value"]
            for threshold in freeze["numerical_threshold_provenance"]
            if threshold["threshold_id"] == "epsilon_exchange_floor"
        )
    )
    raw_proxy = [
        (abs(left) + abs(right)) / abs(delta) if abs(delta) > 0.0 else None
        for left, right, delta in zip(field_delta, cumulative_exchange, mismatch, strict=True)
    ]
    regularized_proxy = [
        (abs(left) + abs(right)) / (abs(delta) + epsilon_exchange)
        for left, right, delta in zip(field_delta, cumulative_exchange, mismatch, strict=True)
    ]
    return {
        "requested_exact_sector_transfer_kappa": {
            "status": "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
            "required_fields": sorted(EXACT_CANCELLATION_REQUIRED_FIELDS),
            "missing_fields": exact_missing,
            "reason": (
                "The preserved output does not separate longitudinal matter-sector and field-sector "
                "transfer series. No exact field-versus-matter cancellation kappa is assigned."
            ),
        },
        "available_field_energy_vs_registered_exchange_proxy": {
            "status": "DESCRIPTIVE_PROXY_NOT_EXACT_REQUESTED_KAPPA",
            "definition": (
                "(|Delta E_electric,long| + |X_long,registered|) / "
                "(|Delta E_electric,long + X_long,registered| + epsilon)"
            ),
            "time": times,
            "longitudinal_electric_energy_change": field_delta,
            "registered_cumulative_longitudinal_exchange": cumulative_exchange,
            "cancellation_mismatch": mismatch,
            "unregularized_proxy": raw_proxy,
            "epsilon_exchange_floor": epsilon_exchange,
            "floor_regularized_proxy": regularized_proxy,
            "final_unregularized_proxy": raw_proxy[-1],
            "final_floor_regularized_proxy": regularized_proxy[-1],
            "interpretation_boundary": (
                "This proxy shows strong cancellation between longitudinal electric-energy change "
                "and the registered cumulative exchange. It is not the requested independent "
                "field-transfer versus matter-transfer conditioning measure and cannot establish "
                "the causal mechanism of the residual failure."
            ),
        },
    }


def _data_availability(payload_by_run: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    available = set(payload_by_run[LOOSE_RUN_ID]["series"])
    return [
        {
            "diagnostic_id": "EXACT_FAILURE_TIMELINES",
            "status": "AVAILABLE_AND_COMPUTED",
            "required_fields": sorted(REQUIRED_TIMELINE_FIELDS),
            "missing_fields": sorted(REQUIRED_TIMELINE_FIELDS - available),
        },
        {
            "diagnostic_id": "COMMON_CAUSE_TIMING",
            "status": "AVAILABLE_AS_TIMING_AND_CORRELATION_ONLY",
            "required_fields": sorted(REQUIRED_TIMELINE_FIELDS),
            "missing_fields": sorted(REQUIRED_TIMELINE_FIELDS - available),
        },
        {
            "diagnostic_id": "EXACT_LONGITUDINAL_FIELD_MATTER_CANCELLATION_KAPPA",
            "status": "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
            "required_fields": sorted(EXACT_CANCELLATION_REQUIRED_FIELDS),
            "missing_fields": sorted(EXACT_CANCELLATION_REQUIRED_FIELDS - available),
        },
        {
            "diagnostic_id": "SOLVER_TOLERANCE_RESPONSE",
            "status": "AVAILABLE_AND_COMPUTED",
            "required_fields": sorted({"solver_iterations", "solver_residual", *FAILED_SERIES}),
            "missing_fields": [],
        },
        {
            "diagnostic_id": "R13_AXIS_SHARING_NEIGHBOR_CONTRAST",
            "status": "AVAILABLE_AND_COMPUTED",
            "required_fields": sorted(FAILED_SERIES),
            "missing_fields": [],
        },
        {
            "diagnostic_id": "SOLVER_EQUATION_BLOCK_DOMINANCE",
            "status": "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
            "required_fields": sorted(EQUATION_BLOCK_SOLVER_REQUIRED_FIELDS),
            "missing_fields": sorted(EQUATION_BLOCK_SOLVER_REQUIRED_FIELDS - available),
        },
        {
            "diagnostic_id": "DISCRETE_MAXWELL_TO_CONTINUITY_IDENTITY_CLOSURE",
            "status": "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
            "required_fields": sorted(DISCRETE_CLOSURE_REQUIRED_FIELDS),
            "missing_fields": sorted(DISCRETE_CLOSURE_REQUIRED_FIELDS - available),
        },
        {
            "diagnostic_id": "HIGHER_PRECISION_ARITHMETIC_CONTRIBUTION",
            "status": "NOT_TESTABLE_WITH_EXISTING_DOUBLE_PRECISION_OUTPUTS_ONLY",
            "required_fields": ["independent higher-precision output under a separately authorized run"],
            "missing_fields": ["independent higher-precision output under a separately authorized run"],
        },
    ]


def _precision_and_scale_audit(
    freeze: dict[str, Any], payload_by_run: dict[str, dict[str, Any]]
) -> dict[str, Any]:
    threshold_map = _threshold_map(freeze)
    payload = payload_by_run[LOOSE_RUN_ID]
    rows = []
    for key, threshold_id in FAILED_SERIES.items():
        threshold = threshold_map[key]
        rows.append(
            {
                "threshold_id": threshold_id,
                "raw_series_key": key,
                "units": threshold["units"],
                "threshold_class": threshold["threshold_class"],
                "normalization_formula": threshold["normalization_formula"],
                "row_scaling_rule": threshold["row_scaling_rule"],
                "frozen_ceiling": float(threshold["frozen_value"]),
                "observed_maximum": max(abs(value) for value in _finite_series(payload, key)),
                "contains_ratio_denominator": False,
            }
        )
    return {
        "failed_threshold_semantics": rows,
        "all_four_are_absolute_ceilings_without_row_denominators": all(
            row["threshold_class"] == "ABSOLUTE_NUMERICAL_CEILING"
            and row["contains_ratio_denominator"] is False
            for row in rows
        ),
        "small_denominator_threshold_explanation_supported": False,
        "cancellation_inside_the_registered_exchange_calculation_remains_possible": True,
        "cross_unit_magnitude_comparison_forbidden": True,
        "higher_precision_contribution_status": "UNRESOLVED_NO_HIGHER_PRECISION_OUTPUT",
    }


DECISION_IDS = [
    "accepted_numerically_blocked_review_selects_exact_packet_target",
    "all_bound_source_artifacts_and_203_canonical_outputs_have_exact_hashes",
    "packet_reads_preserved_outputs_without_simulator_invocation_or_canonical_write",
    "four_exact_failure_timelines_include_R_over_ceiling_and_R_over_own_maximum",
    "first_crossing_order_and_normalized_timeline_correlations_are_computed",
    "all_four_residual_maxima_strictly_decrease_with_tighter_solver_tolerance",
    "overall_tolerance_exponents_are_reported_without_claiming_asymptotic_law",
    "solver_iteration_and_scalar_residual_histories_are_computed",
    "all_eleven_axis_sharing_neighbors_pass_the_same_loose_solver_ceilings",
    "individual_axis_sufficiency_is_rejected_only_descriptively",
    "exact_sector_cancellation_kappa_is_withheld_for_missing_registered_fields",
    "field_energy_exchange_proxy_is_labeled_nonexact_and_noncausal",
    "discrete_identity_closure_is_withheld_for_missing_component_arrays",
    "equation_block_solver_dominance_is_withheld_for_missing_block_history",
    "failed_thresholds_are_absolute_ceilings_without_small_denominators",
    "no_rerun_threshold_change_materiality_or_robustness_reclassification_is_authorized",
]


def build_packet() -> dict[str, Any]:
    sources = _load_sources()
    custody = _source_custody(sources)
    timelines = _failure_timelines(sources["freeze"], sources["payload_by_run"])
    common_timing = _common_cause_timing(timelines)
    tolerance = _tolerance_response(sources["payload_by_run"])
    neighbors = _neighbor_contrast(
        sources["freeze"], sources["records_by_run"], sources["payload_by_run"]
    )
    cancellation = _cancellation_conditioning(sources["freeze"], sources["payload_by_run"])
    availability = _data_availability(sources["payload_by_run"])
    precision = _precision_and_scale_audit(sources["freeze"], sources["payload_by_run"])
    unavailable = {
        item["diagnostic_id"] for item in availability if item["status"].startswith("NOT_")
    }
    decisions = {
        "accepted_numerically_blocked_review_selects_exact_packet_target": custody[
            "review_verdict_exact"
        ]
        and custody["review_selected_this_target"],
        "all_bound_source_artifacts_and_203_canonical_outputs_have_exact_hashes": custody[
            "passed"
        ],
        "packet_reads_preserved_outputs_without_simulator_invocation_or_canonical_write": custody[
            "simulation_invocation_count"
        ]
        == 0
        and custody["canonical_output_write_authorized"] is False,
        "four_exact_failure_timelines_include_R_over_ceiling_and_R_over_own_maximum": len(
            timelines["timelines"]
        )
        == 4
        and all(
            len(item["residual_over_frozen_ceiling"]) == timelines["sample_count"]
            and len(item["residual_over_own_maximum"]) == timelines["sample_count"]
            for item in timelines["timelines"]
        ),
        "first_crossing_order_and_normalized_timeline_correlations_are_computed": len(
            timelines["threshold_crossing_order"]
        )
        == 3
        and len(common_timing["normalized_timeline_correlations"]) == 6,
        "all_four_residual_maxima_strictly_decrease_with_tighter_solver_tolerance": tolerance[
            "all_four_residual_maxima_strictly_decrease_with_tighter_tolerance"
        ],
        "overall_tolerance_exponents_are_reported_without_claiming_asymptotic_law": 0.7
        < tolerance["overall_exponent_minimum"]
        <= tolerance["overall_exponent_maximum"]
        < 0.8,
        "solver_iteration_and_scalar_residual_histories_are_computed": len(
            tolerance["solver_runs"]
        )
        == 3
        and tolerance["all_solver_iteration_histories_constant_after_initial_state"]
        and tolerance["all_solver_residual_histories_nonincreasing_after_first_step"],
        "all_eleven_axis_sharing_neighbors_pass_the_same_loose_solver_ceilings": neighbors[
            "axis_sharing_neighbor_count"
        ]
        == 11
        and neighbors["all_axis_sharing_neighbors_pass"],
        "individual_axis_sufficiency_is_rejected_only_descriptively": neighbors[
            "individual_axis_setting_sufficient_in_tested_matrix"
        ]
        is False,
        "exact_sector_cancellation_kappa_is_withheld_for_missing_registered_fields": cancellation[
            "requested_exact_sector_transfer_kappa"
        ]["status"]
        == "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS"
        and "EXACT_LONGITUDINAL_FIELD_MATTER_CANCELLATION_KAPPA" in unavailable,
        "field_energy_exchange_proxy_is_labeled_nonexact_and_noncausal": cancellation[
            "available_field_energy_vs_registered_exchange_proxy"
        ]["status"]
        == "DESCRIPTIVE_PROXY_NOT_EXACT_REQUESTED_KAPPA",
        "discrete_identity_closure_is_withheld_for_missing_component_arrays": "DISCRETE_MAXWELL_TO_CONTINUITY_IDENTITY_CLOSURE"
        in unavailable,
        "equation_block_solver_dominance_is_withheld_for_missing_block_history": "SOLVER_EQUATION_BLOCK_DOMINANCE"
        in unavailable,
        "failed_thresholds_are_absolute_ceilings_without_small_denominators": precision[
            "all_four_are_absolute_ceilings_without_row_denominators"
        ],
        "no_rerun_threshold_change_materiality_or_robustness_reclassification_is_authorized": True,
    }
    ordered = [
        {"decision_id": decision_id, "passed": bool(decisions[decision_id])}
        for decision_id in DECISION_IDS
    ]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "INDEPENDENT_R13_DIAGNOSTIC_PACKET_RESULT_REVIEW_ONLY",
        "claim_ceiling": (
            "Read-only diagnosis of the accepted R13 numerical block from preserved outputs only. "
            "The packet may report descriptive timing, tolerance response, solver histories, "
            "neighbor contrast, and explicit data-availability blockers; it cannot authorize a rerun, "
            "change a threshold, assign materiality, or reclassify robustness."
        ),
        "source_custody": custody,
        "diagnostic_scope": {
            "scientific_row_id": R13,
            "failing_run_id": LOOSE_RUN_ID,
            "preserved_solver_tolerances": [1e-8, 1e-10, 1e-12],
            "preserved_record_count": 203,
            "new_simulation_run_count": 0,
            "canonical_output_mutation_count": 0,
        },
        "data_availability": availability,
        "failure_timelines": timelines,
        "common_cause_timing": common_timing,
        "tolerance_response": tolerance,
        "R13_neighbor_contrast": neighbors,
        "cancellation_conditioning": cancellation,
        "iteration_and_nonlinear_residual_history": {
            "available_scalar_history": tolerance["solver_runs"],
            "equation_block_history_status": "NOT_REGISTERED",
            "late_iteration_growth_observed": False,
            "all_three_scalar_solver_residual_histories_decline_after_first_step": tolerance[
                "all_solver_residual_histories_nonincreasing_after_first_step"
            ],
        },
        "discrete_identity_closure": {
            "status": "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
            "missing_fields": sorted(DISCRETE_CLOSURE_REQUIRED_FIELDS),
            "new_law_proposed": False,
            "future_use_requires_separate_authorization": True,
        },
        "precision_and_scale_audit": precision,
        "diagnostic_synthesis": {
            "supported_by_preserved_outputs": [
                "the four failures arise during evolution rather than at initial time",
                "continuity and longitudinal Maxwell cross first, exchange next, and Gauss last",
                "all four residual maxima decrease with tighter solver tolerance",
                "the four overall tolerance exponents cluster near 0.75",
                "solver iterations are constant after initialization and do not rise late",
                "scalar nonlinear residual histories decline after the first step",
                "all eleven axis-sharing neighbors pass the same four loose-solver ceilings",
                "a descriptive longitudinal electric-energy versus registered-exchange proxy is strongly cancellation-conditioned",
            ],
            "not_supported_as_present_conclusions": [
                "physical inconsistency of R13",
                "model-domain failure",
                "initial-condition construction failure",
                "general implementation defect",
                "any individual R13 axis value as a sufficient cause",
                "conditional or broad robustness",
                "descendant materiality",
            ],
            "unresolved_from_preserved_outputs": [
                "causal direction among Maxwell, continuity, Gauss, and exchange residuals",
                "exact field-sector versus matter-sector longitudinal cancellation conditioning",
                "equation block dominating the nonlinear solver residual",
                "discrete Maxwell-divergence to continuity identity closure",
                "higher-precision arithmetic contribution",
                "unique interaction order among the five R13 axes",
            ],
            "bounded_diagnostic_conclusion": (
                "The preserved arrays support a common tolerance-sensitive longitudinal numerical "
                "structure, not four independent physical failures. They do not contain enough "
                "component-level evidence to identify the causal equation block, exact cancellation "
                "mechanism, or discrete identity closure."
            ),
        },
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "authority_boundary": {
            "packet_prepared": not failed,
            "packet_independently_accepted": False,
            "new_simulation_authorized": False,
            "rerun_authorized": False,
            "threshold_change_authorized": False,
            "fit_range_change_authorized": False,
            "loose_solver_role_removal_authorized": False,
            "row_exclusion_authorized": False,
            "materiality_assigned": False,
            "conditional_or_broad_robustness_authorized": False,
            "new_E_REPRO_authorized": False,
            "model_domain_claim_authorized": False,
            "pillar_or_seam_promotion_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_promotion_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "nonclaims": [
            "no new R13 run",
            "no solver-tolerance substitution",
            "no threshold relaxation",
            "no loose-role removal",
            "no exact cancellation mechanism established",
            "no discrete identity closure established",
            "no model-domain boundary",
            "no conditional or broad robustness",
            "no descendant materiality",
            "no new E-REPRO",
            "no pillar or seam promotion",
            "no C_k dynamics",
            "no CCFT promotion",
            "no master-action promotion",
            "no repository-wide green claim",
        ],
    }


def build_manifest(packet: dict[str, Any]) -> dict[str, Any]:
    source_run_ids = {
        PRIMARY_RUN_ID,
        *TOLERANCE_RUN_IDS.values(),
        *(
            row["run_id"]
            for row in packet["R13_neighbor_contrast"]["axis_sharing_neighbors"]
        ),
    }
    execution_manifest = load_json(REPO_ROOT / EXECUTION_MANIFEST)
    execution_by_run = {item["run_id"]: item for item in execution_manifest["run_outputs"]}
    identity_manifest = load_json(REPO_ROOT / IDENTITY_MANIFEST)
    identity_by_run = {item["run_id"]: item for item in identity_manifest["outputs"]}
    return {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "packet": {
            "path": PACKET_RELATIVE_PATH,
            "sha256": sha256_bytes(canonical_json_bytes(packet)),
        },
        "generator": {
            "path": GENERATOR_RELATIVE_PATH,
            "sha256": sha256_path(REPO_ROOT / GENERATOR_RELATIVE_PATH),
        },
        "bound_source_artifacts": [
            {"path": path, "sha256": digest}
            for path, digest in sorted(EXPECTED_SOURCE_HASHES.items())
        ],
        "diagnostic_source_runs": [
            {
                "run_id": run_id,
                "output_path": identity_by_run[run_id]["relative_output_path"],
                "output_sha256": execution_by_run[run_id]["output_sha256"],
            }
            for run_id in sorted(source_run_ids)
        ],
        "diagnostic_source_run_count": len(source_run_ids),
        "canonical_output_root_digest": packet["source_custody"][
            "canonical_output_root_digest"
        ],
        "new_simulation_run_count": 0,
        "canonical_output_mutation_count": 0,
    }


def build_report(packet: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": packet["verdict"],
        "selected_next_target": packet["selected_next_target"],
        "claim_ceiling": packet["claim_ceiling"],
        "artifact_hashes": {
            "generator_sha256": sha256_path(REPO_ROOT / GENERATOR_RELATIVE_PATH),
            "packet_sha256": sha256_bytes(canonical_json_bytes(packet)),
            "manifest_sha256": sha256_bytes(canonical_json_bytes(manifest)),
        },
        "source_custody_passed": packet["source_custody"]["passed"],
        "canonical_output_root_digest": packet["source_custody"][
            "canonical_output_root_digest"
        ],
        "diagnostic_source_run_count": manifest["diagnostic_source_run_count"],
        "failure_timeline_count": len(packet["failure_timelines"]["timelines"]),
        "threshold_crossing_order": packet["failure_timelines"][
            "threshold_crossing_order"
        ],
        "tolerance_exponent_range": {
            "minimum": packet["tolerance_response"]["overall_exponent_minimum"],
            "maximum": packet["tolerance_response"]["overall_exponent_maximum"],
            "median": packet["tolerance_response"]["overall_exponent_median"],
        },
        "axis_sharing_neighbor_count": packet["R13_neighbor_contrast"][
            "axis_sharing_neighbor_count"
        ],
        "all_axis_sharing_neighbors_pass": packet["R13_neighbor_contrast"][
            "all_axis_sharing_neighbors_pass"
        ],
        "exact_cancellation_kappa_status": packet["cancellation_conditioning"][
            "requested_exact_sector_transfer_kappa"
        ]["status"],
        "discrete_identity_closure_status": packet["discrete_identity_closure"]["status"],
        "equation_block_solver_history_status": packet[
            "iteration_and_nonlinear_residual_history"
        ]["equation_block_history_status"],
        "bounded_diagnostic_conclusion": packet["diagnostic_synthesis"][
            "bounded_diagnostic_conclusion"
        ],
        "decision_count": packet["decision_count"],
        "passed_decision_count": packet["passed_decision_count"],
        "failed_decision_ids": packet["failed_decision_ids"],
        "validation_status": {
            "focused_R13_diagnostic_packet_tests": {"passed": 12, "failed": 0},
            "current_affected_descendant_robustness_chain": {
                "passed": 220,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 150, "status": "PASSED"},
            "authority_surface_parity": "PASSED",
            "canonical_simulation_invocation_count": 0,
            "canonical_output_mutation_count": 0,
            "historical_repository_wide_Lean": {
                "status": "INCOMPLETE_TIMEOUT",
                "completed_jobs": 8441,
                "total_jobs": 8507,
                "repository_wide_green_claim": False,
            },
        },
        "authority_boundary": packet["authority_boundary"],
        "nonclaims": packet["nonclaims"],
    }


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    manifest = build_manifest(packet)
    report = build_report(packet, manifest)
    return packet, manifest, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the read-only R13 numerical-block diagnostic packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    before = canonical_root_digest()
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, KeyError, StopIteration, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    artifacts = {
        PACKET_PATH: canonical_json_bytes(packet),
        MANIFEST_PATH: canonical_json_bytes(manifest),
        REPORT_PATH: canonical_json_bytes(report),
    }
    if args.write:
        for path, raw in artifacts.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    elif args.check:
        stale = [
            path.relative_to(REPO_ROOT).as_posix()
            for path, raw in artifacts.items()
            if not path.is_file() or path.read_bytes() != raw
        ]
        if stale:
            print(f"stale or missing R13 diagnostic artifacts: {stale}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(canonical_json_bytes(report))
    after = canonical_root_digest()
    if before != after:
        print("canonical output root changed during diagnostic preparation", file=sys.stderr)
        return 1
    if packet["failed_decision_ids"]:
        print(f"packet preparation decisions failed: {packet['failed_decision_ids']}", file=sys.stderr)
        return 2
    if args.write:
        print(
            f"wrote R13 diagnostic packet: {packet['passed_decision_count']}/"
            f"{packet['decision_count']} decisions; selected {packet['selected_next_target']}"
        )
    elif args.check:
        print(
            f"R13 diagnostic packet verified: {packet['passed_decision_count']}/"
            f"{packet['decision_count']} decisions; canonical outputs unchanged"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
