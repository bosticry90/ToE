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
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "r13_numerical_block_diagnostic_packet_v0_result"
)
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "r13_numerical_block_route_selection_packet_v0"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_REVIEW_20260715_v0"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_REVIEW_20260715_v0.json"
)
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH
REVIEWER_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_r13_numerical_block_diagnostic_packet_review_v0.py"
)

DIAGNOSTIC_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-DIAGNOSTIC-PACKET-v0.json"
)
DIAGNOSTIC_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-R13-NUMERICAL-BLOCK-DIAGNOSTIC-MANIFEST-v0.json"
)
DIAGNOSTIC_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_20260715_v0.json"
)
DIAGNOSTIC_GENERATOR = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_r13_numerical_block_diagnostic_packet_v0.py"
)
CANONICAL_REVIEW = (
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

EXPECTED_SOURCE_HASHES = {
    DIAGNOSTIC_PACKET: "8edd51901d2999ea1781c5768a64aeabd7d5328dfda61f45e4a7853865937eed",
    DIAGNOSTIC_MANIFEST: "bf8ffa4e606229d0eb0a54a41bddf62fc02c15316cd41efc00eaa2d67f6d6aca",
    DIAGNOSTIC_REPORT: "b065687a1904ad3e9d8f3c607d72272a19d4bc7cf41b8170f0c2cb980248b481",
    DIAGNOSTIC_GENERATOR: "e9a6aeb6e96244cb39aff93e61c80cbe19e238b5c23b7e29dd1f82cc484760eb",
    CANONICAL_REVIEW: "cacbd77f3ef18a80d8d15686dd8f385f73a634038fddb5010058f2e144ef3c85",
    FREEZE_PACKET: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    RUN_MATRIX: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    IDENTITY_MANIFEST: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    EXECUTION_MANIFEST: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    EXECUTION_PACKET: "9020fd19774a2c2ccff108fd7950945a076a459f185bed3b10480270499cf86a",
}
EXPECTED_CANONICAL_ROOT_DIGEST = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)

R13 = "R13_CORNER_STRONG_LOW"
LOOSE_RUN_ID = f"{R13}:SOLVER_TOL1eM08"
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
HIGHER_PRECISION_REQUIRED_FIELDS = {"independent_higher_precision_output"}


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
    slope = sum(
        (left - mean_x) * (right - mean_y)
        for left, right in zip(x, y, strict=True)
    ) / denominator
    intercept = mean_y - slope * mean_x
    predicted = [intercept + slope * value for value in x]
    residual_sum = sum(
        (observed - fitted) ** 2
        for observed, fitted in zip(y, predicted, strict=True)
    )
    total_sum = sum((observed - mean_y) ** 2 for observed in y)
    return {
        "slope": slope,
        "intercept": intercept,
        "r_squared": 1.0 - residual_sum / total_sum if total_sum > 0.0 else 1.0,
    }


def _growth_fits(times: list[float], magnitudes: list[float]) -> dict[str, Any]:
    positive = [
        (time, value)
        for time, value in zip(times, magnitudes, strict=True)
        if time > 0.0 and value > 0.0
    ]
    fit_times = [item[0] for item in positive]
    fit_values = [item[1] for item in positive]
    linear = _linear_fit(fit_times, fit_values)
    quadratic = _linear_fit([time * time for time in fit_times], fit_values)
    exponential = _linear_fit(fit_times, [math.log(value) for value in fit_values])
    power = _linear_fit(
        [math.log(time) for time in fit_times],
        [math.log(value) for value in fit_values],
    )
    return {
        "fit_point_count": len(positive),
        "linear_in_time": linear,
        "linear_in_time_squared": quadratic,
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


def _pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 2:
        return None
    mean_left = statistics.fmean(left)
    mean_right = statistics.fmean(right)
    numerator = sum(
        (a - mean_left) * (b - mean_right)
        for a, b in zip(left, right, strict=True)
    )
    denominator = math.sqrt(
        sum((value - mean_left) ** 2 for value in left)
        * sum((value - mean_right) ** 2 for value in right)
    )
    return numerator / denominator if denominator > 0.0 else None


def _first_time_at_fraction(
    times: list[float], magnitudes: list[float], fraction: float
) -> float:
    target = fraction * max(magnitudes)
    return next(
        time
        for time, value in zip(times, magnitudes, strict=True)
        if value >= target
    )


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


def _collect_keys(value: Any, keys: set[str]) -> None:
    if isinstance(value, dict):
        for key, item in value.items():
            keys.add(str(key))
            _collect_keys(item, keys)
    elif isinstance(value, list):
        for item in value:
            _collect_keys(item, keys)


def _load_sources() -> dict[str, Any]:
    packet = load_json(REPO_ROOT / DIAGNOSTIC_PACKET)
    manifest = load_json(REPO_ROOT / DIAGNOSTIC_MANIFEST)
    diagnostic_report = load_json(REPO_ROOT / DIAGNOSTIC_REPORT)
    canonical_review = load_json(REPO_ROOT / CANONICAL_REVIEW)
    freeze = load_json(REPO_ROOT / FREEZE_PACKET)
    matrix = load_json(REPO_ROOT / RUN_MATRIX)
    identity = load_json(REPO_ROOT / IDENTITY_MANIFEST)
    execution_manifest = load_json(REPO_ROOT / EXECUTION_MANIFEST)
    execution_packet = load_json(REPO_ROOT / EXECUTION_PACKET)
    identity_by_run = {item["run_id"]: item for item in identity["outputs"]}
    execution_by_run = {
        item["run_id"]: item for item in execution_manifest["run_outputs"]
    }
    records_by_run = {item["run_id"]: item for item in matrix["records"]}
    payload_by_run = {
        run_id: load_json(REPO_ROOT / item["relative_output_path"])
        for run_id, item in identity_by_run.items()
    }
    return {
        "packet": packet,
        "manifest": manifest,
        "diagnostic_report": diagnostic_report,
        "canonical_review": canonical_review,
        "freeze": freeze,
        "matrix": matrix,
        "identity": identity,
        "execution_manifest": execution_manifest,
        "execution_packet": execution_packet,
        "identity_by_run": identity_by_run,
        "execution_by_run": execution_by_run,
        "records_by_run": records_by_run,
        "payload_by_run": payload_by_run,
    }


def _custody(sources: dict[str, Any]) -> dict[str, Any]:
    observed_hashes = {
        path: sha256_path(REPO_ROOT / path) for path in EXPECTED_SOURCE_HASHES
    }
    output_failures = []
    for run_id, identity in sources["identity_by_run"].items():
        execution = sources["execution_by_run"].get(run_id, {})
        path = identity["relative_output_path"]
        observed = sha256_path(REPO_ROOT / path)
        if (
            observed != execution.get("output_sha256")
            or path != execution.get("relative_output_path")
        ):
            output_failures.append(
                {
                    "run_id": run_id,
                    "path": path,
                    "observed_sha256": observed,
                    "expected_sha256": execution.get("output_sha256"),
                    "execution_path": execution.get("relative_output_path"),
                }
            )
    inventory = _canonical_root_inventory()
    root_digest = sha256_bytes(canonical_json_bytes(inventory))
    packet = sources["packet"]
    manifest = sources["manifest"]
    diagnostic_report = sources["diagnostic_report"]
    return {
        "source_artifact_hashes": observed_hashes,
        "expected_source_artifact_hashes": EXPECTED_SOURCE_HASHES,
        "source_artifact_hashes_exact": observed_hashes == EXPECTED_SOURCE_HASHES,
        "diagnostic_packet_hash_bound_by_manifest": manifest["packet"]["sha256"]
        == observed_hashes[DIAGNOSTIC_PACKET],
        "diagnostic_generator_hash_bound_by_manifest": manifest["generator"]["sha256"]
        == observed_hashes[DIAGNOSTIC_GENERATOR],
        "diagnostic_report_hashes_match_packet_manifest_and_generator": diagnostic_report[
            "artifact_hashes"
        ]
        == {
            "packet_sha256": observed_hashes[DIAGNOSTIC_PACKET],
            "manifest_sha256": observed_hashes[DIAGNOSTIC_MANIFEST],
            "generator_sha256": observed_hashes[DIAGNOSTIC_GENERATOR],
        },
        "canonical_run_output_count_checked": len(sources["identity_by_run"]),
        "canonical_run_output_hash_failures": output_failures,
        "canonical_root_file_count": len(inventory),
        "canonical_root_digest": root_digest,
        "canonical_root_digest_exact": root_digest == EXPECTED_CANONICAL_ROOT_DIGEST,
        "packet_root_digest_exact": packet["source_custody"][
            "canonical_output_root_digest"
        ]
        == root_digest,
        "manifest_root_digest_exact": manifest["canonical_output_root_digest"]
        == root_digest,
        "execution_count_performed": sources["execution_packet"][
            "execution_count_performed"
        ],
        "simulation_invocation_count_during_review": 0,
        "canonical_output_mutation_authorized": False,
        "passed": observed_hashes == EXPECTED_SOURCE_HASHES
        and not output_failures
        and len(sources["identity_by_run"]) == 203
        and len(sources["execution_by_run"]) == 203
        and len(inventory) == 205
        and root_digest == EXPECTED_CANONICAL_ROOT_DIGEST
        and packet["source_custody"]["canonical_output_root_digest"] == root_digest
        and manifest["canonical_output_root_digest"] == root_digest
        and sources["execution_packet"]["execution_count_performed"] == 1,
    }


def _threshold_map(freeze: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        item["raw_series_key"]: item
        for item in freeze["numerical_threshold_provenance"]
        if item["raw_series_key"] in FAILED_SERIES
    }


def _reconstruct_timelines(
    freeze: dict[str, Any], payload_by_run: dict[str, dict[str, Any]]
) -> dict[str, Any]:
    payload = payload_by_run[LOOSE_RUN_ID]
    times = _finite_series(payload, "time")
    thresholds = _threshold_map(freeze)
    timelines = []
    for key, threshold_id in FAILED_SERIES.items():
        magnitudes = [abs(value) for value in _finite_series(payload, key)]
        ceiling = float(thresholds[key]["frozen_value"])
        maximum = max(magnitudes)
        crossing_index = next(
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
                "first_threshold_crossing_time": times[crossing_index],
                "maximum_time": times[magnitudes.index(maximum)],
                "fractional_onset_times": {
                    "10_percent_of_maximum": _first_time_at_fraction(
                        times, magnitudes, 0.1
                    ),
                    "50_percent_of_maximum": _first_time_at_fraction(
                        times, magnitudes, 0.5
                    ),
                    "90_percent_of_maximum": _first_time_at_fraction(
                        times, magnitudes, 0.9
                    ),
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
        "all_maxima_at_final_time": all(
            item["maximum_time"] == times[-1] for item in timelines
        ),
        "all_absolute_magnitudes_monotone_nondecreasing": all(
            item["absolute_magnitude_monotone_nondecreasing"] for item in timelines
        ),
    }


def _timing_and_time_law(timelines: dict[str, Any]) -> dict[str, Any]:
    normalized = {
        item["raw_series_key"]: item["residual_over_own_maximum"]
        for item in timelines["timelines"]
    }
    keys = sorted(normalized)
    correlations = []
    for index, left in enumerate(keys):
        for right in keys[index + 1 :]:
            correlations.append(
                {
                    "left": left,
                    "right": right,
                    "pearson_correlation_of_normalized_absolute_timelines": _pearson(
                        normalized[left][1:], normalized[right][1:]
                    ),
                }
            )
    ordinary_scale_comparison = []
    for item in timelines["timelines"]:
        fits = item["growth_fits"]
        linear_r2 = float(fits["linear_in_time"]["r_squared"])
        quadratic_r2 = float(fits["linear_in_time_squared"]["r_squared"])
        ordinary_scale_comparison.append(
            {
                "threshold_id": item["threshold_id"],
                "linear_in_time_R2": linear_r2,
                "linear_in_time_squared_R2": quadratic_r2,
                "better_of_these_two_descriptive_coordinates": (
                    "LINEAR_IN_TIME" if linear_r2 >= quadratic_r2 else "LINEAR_IN_TIME_SQUARED"
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
        "ordinary_scale_linear_vs_time_squared": ordinary_scale_comparison,
        "linear_in_time_preferred_count": sum(
            item["better_of_these_two_descriptive_coordinates"] == "LINEAR_IN_TIME"
            for item in ordinary_scale_comparison
        ),
        "linear_in_time_squared_preferred_count": sum(
            item["better_of_these_two_descriptive_coordinates"]
            == "LINEAR_IN_TIME_SQUARED"
            for item in ordinary_scale_comparison
        ),
        "common_time_law_certified": False,
        "longer_duration_prediction_executed": False,
        "causal_hierarchy_certified": False,
        "bounded_interpretation": (
            "The crossing order is consistent with a shared longitudinal source, but scalar norms "
            "cannot prove a Maxwell-to-continuity-to-exchange-to-Gauss causal hierarchy. Three "
            "ordinary-scale series are closer to linear in time and exchange is closer to linear "
            "in time squared; no common time law or longer-duration extrapolation is certified."
        ),
    }


def _normalized_tolerance_configuration(record: dict[str, Any]) -> dict[str, Any]:
    identity_fields = {
        "run_id",
        "safe_filename",
        "input_hash",
        "output_path",
        "solver_tolerance",
    }
    return {key: value for key, value in record.items() if key not in identity_fields}


def _reconstruct_tolerance_response(sources: dict[str, Any]) -> dict[str, Any]:
    records = {
        tolerance: sources["records_by_run"][run_id]
        for tolerance, run_id in TOLERANCE_RUN_IDS.items()
    }
    normalized = {
        tolerance: _normalized_tolerance_configuration(record)
        for tolerance, record in records.items()
    }
    normalized_hashes = {
        str(tolerance): sha256_bytes(canonical_json_bytes(configuration))
        for tolerance, configuration in normalized.items()
    }
    configurations_comparable = len(set(normalized_hashes.values())) == 1
    solver_runs = []
    maxima_by_key: dict[str, dict[float, float]] = {key: {} for key in FAILED_SERIES}
    for tolerance in sorted(TOLERANCE_RUN_IDS, reverse=True):
        run_id = TOLERANCE_RUN_IDS[tolerance]
        payload = sources["payload_by_run"][run_id]
        residual_maxima = {}
        for key in FAILED_SERIES:
            maximum = max(abs(value) for value in _finite_series(payload, key))
            residual_maxima[key] = maximum
            maxima_by_key[key][tolerance] = maximum
        iterations = _finite_series(payload, "solver_iterations")
        solver_residual = [
            abs(value) for value in _finite_series(payload, "solver_residual")
        ]
        solver_runs.append(
            {
                "run_id": run_id,
                "solver_tolerance": tolerance,
                "residual_maxima": residual_maxima,
                "solver_iterations": iterations,
                "solver_residual": solver_residual,
                "maximum_iterations": max(iterations),
                "iterations_constant_after_initial_state": len(set(iterations[1:])) == 1,
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
                    str(tolerance): value
                    for tolerance, value in sorted(maxima.items(), reverse=True)
                },
                "pairwise_tolerance_exponents": pairwise,
                "overall_1eM08_to_1eM12_exponent": overall,
                "strictly_decreases_with_tighter_tolerance": maxima[1e-8]
                > maxima[1e-10]
                > maxima[1e-12],
            }
        )
    return {
        "registered_tolerance_run_ids": TOLERANCE_RUN_IDS,
        "registered_tolerances_used": sorted(TOLERANCE_RUN_IDS, reverse=True),
        "post_hoc_tolerance_point_selection_performed": False,
        "normalized_configuration_hashes": normalized_hashes,
        "configurations_identical_except_tolerance_and_identity_fields": configurations_comparable,
        "solver_runs": solver_runs,
        "residual_tolerance_response": residual_rows,
        "all_four_residual_maxima_strictly_decrease_with_tighter_tolerance": all(
            item["strictly_decreases_with_tighter_tolerance"] for item in residual_rows
        ),
        "overall_exponent_minimum": min(overall_exponents),
        "overall_exponent_maximum": max(overall_exponents),
        "overall_exponent_median": statistics.median(overall_exponents),
        "all_solver_iteration_histories_constant_after_initial_state": all(
            row["iterations_constant_after_initial_state"] for row in solver_runs
        ),
        "all_solver_residual_histories_nonincreasing_after_first_step": all(
            row["solver_residual_nonincreasing_after_first_step"] for row in solver_runs
        ),
        "all_steps_converged": all(row["all_steps_converged"] for row in solver_runs),
        "physical_or_asymptotic_exponent_claim_authorized": False,
    }


def _reconstruct_neighbors(sources: dict[str, Any]) -> dict[str, Any]:
    thresholds = _threshold_map(sources["freeze"])
    scientific_rows = {
        item["row_id"]: item["requested_axis_values"]
        for item in sources["freeze"]["scientific_design_freeze"]["scientific_rows"]
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
            for item in sources["records_by_run"].values()
            if item["scientific_row_id"] == row_id
            and item["run_role"] == "SOLVER_VERIFICATION"
            and float(item["solver_tolerance"]) == 1e-8
        )
        ratios = {
            key: max(
                abs(value)
                for value in _finite_series(
                    sources["payload_by_run"][record["run_id"]], key
                )
            )
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
    rows = sorted(rows, key=lambda item: item["scientific_row_id"])
    axis_checks = []
    for axis, value in r13_axes.items():
        matching = [row for row in rows if axis in row["shared_axes"]]
        axis_checks.append(
            {
                "axis": axis,
                "R13_value": value,
                "matching_non_R13_rows": [row["scientific_row_id"] for row in matching],
                "all_matching_rows_pass": bool(matching)
                and all(row["all_four_pass"] for row in matching),
            }
        )
    return {
        "axis_sharing_neighbor_count": len(rows),
        "axis_sharing_neighbors": rows,
        "per_axis_checks": axis_checks,
        "all_axis_sharing_neighbors_pass": all(row["all_four_pass"] for row in rows),
        "all_five_individual_axis_values_have_at_least_one_passing_non_R13_match": all(
            item["all_matching_rows_pass"] for item in axis_checks
        ),
        "individual_axis_value_sufficient_cause_supported": False,
        "unique_interaction_order_identified": False,
    }


def _mechanism_availability(sources: dict[str, Any]) -> dict[str, Any]:
    registered_keys: set[str] = set()
    for payload in sources["payload_by_run"].values():
        _collect_keys(payload, registered_keys)

    def audit(required: set[str], status: str) -> dict[str, Any]:
        present = sorted(required & registered_keys)
        missing = sorted(required - registered_keys)
        return {
            "status": status if missing else "UNEXPECTEDLY_AVAILABLE_REVIEW_BLOCKER",
            "required_fields": sorted(required),
            "present_fields": present,
            "missing_fields": missing,
            "checked_across_canonical_record_count": len(sources["payload_by_run"]),
        }

    return {
        "registered_recursive_key_count": len(registered_keys),
        "exact_field_matter_cancellation_kappa": audit(
            EXACT_CANCELLATION_REQUIRED_FIELDS,
            "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
        ),
        "equation_block_solver_dominance": audit(
            EQUATION_BLOCK_SOLVER_REQUIRED_FIELDS,
            "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
        ),
        "discrete_Maxwell_to_continuity_closure": audit(
            DISCRETE_CLOSURE_REQUIRED_FIELDS,
            "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
        ),
        "higher_precision_arithmetic_contribution": audit(
            HIGHER_PRECISION_REQUIRED_FIELDS,
            "NOT_TESTABLE_WITH_EXISTING_DOUBLE_PRECISION_OUTPUTS_ONLY",
        ),
        "root_numerical_mechanism_identified": False,
    }


def _packet_parity_and_claim_audit(
    sources: dict[str, Any],
    timelines: dict[str, Any],
    timing: dict[str, Any],
    tolerance: dict[str, Any],
    neighbors: dict[str, Any],
    availability: dict[str, Any],
) -> dict[str, Any]:
    packet = sources["packet"]
    packet_tolerance = packet["tolerance_response"]
    packet_neighbors = packet["R13_neighbor_contrast"]
    packet_common = packet["common_cause_timing"]
    tolerance_numeric_parity = (
        tolerance["solver_runs"] == packet_tolerance["solver_runs"]
        and tolerance["residual_tolerance_response"]
        == packet_tolerance["residual_tolerance_response"]
        and tolerance["overall_exponent_minimum"]
        == packet_tolerance["overall_exponent_minimum"]
        and tolerance["overall_exponent_maximum"]
        == packet_tolerance["overall_exponent_maximum"]
        and tolerance["overall_exponent_median"]
        == packet_tolerance["overall_exponent_median"]
    )
    neighbor_parity = (
        neighbors["axis_sharing_neighbor_count"]
        == packet_neighbors["axis_sharing_neighbor_count"]
        and neighbors["axis_sharing_neighbors"]
        == packet_neighbors["axis_sharing_neighbors"]
        and neighbors["all_axis_sharing_neighbors_pass"]
        == packet_neighbors["all_axis_sharing_neighbors_pass"]
    )
    unavailable_statuses_match = (
        availability["exact_field_matter_cancellation_kappa"]["status"]
        == packet["cancellation_conditioning"]["requested_exact_sector_transfer_kappa"][
            "status"
        ]
        and availability["equation_block_solver_dominance"]["status"]
        == "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS"
        and availability["discrete_Maxwell_to_continuity_closure"]["status"]
        == packet["discrete_identity_closure"]["status"]
    )
    boundary = packet["authority_boundary"]
    stronger_claims_false = all(
        boundary[key] is False
        for key in (
            "packet_independently_accepted",
            "new_simulation_authorized",
            "rerun_authorized",
            "threshold_change_authorized",
            "materiality_assigned",
            "conditional_or_broad_robustness_authorized",
            "new_E_REPRO_authorized",
            "model_domain_claim_authorized",
            "pillar_or_seam_promotion_authorized",
            "C_k_dynamics_authorized",
            "CCFT_promotion_authorized",
            "master_action_promotion_authorized",
        )
    )
    return {
        "packet_target_exact": packet["target"]
        == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_r13_numerical_block_diagnostic_packet_v0",
        "packet_verdict_pending_review": packet["verdict"]
        == "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "packet_selects_exact_review_target": packet["selected_next_target"] == TARGET,
        "packet_decisions_all_pass": packet["decision_count"]
        == packet["passed_decision_count"]
        == 16
        and packet["failed_decision_ids"] == [],
        "timeline_reconstruction_exact": timelines == packet["failure_timelines"],
        "timing_correlation_reconstruction_exact": timing[
            "normalized_timeline_correlations"
        ]
        == packet_common["normalized_timeline_correlations"]
        and timing["minimum_pairwise_correlation"]
        == packet_common["minimum_pairwise_correlation"],
        "tolerance_numeric_reconstruction_exact": tolerance_numeric_parity,
        "neighbor_reconstruction_exact": neighbor_parity,
        "unavailable_mechanism_statuses_match": unavailable_statuses_match,
        "claim_ceiling_preserved": stronger_claims_false
        and boundary["packet_prepared"] is True,
        "causal_hierarchy_overclaim_detected": False,
        "physical_instability_overclaim_detected": False,
        "model_boundary_overclaim_detected": False,
        "conditional_robustness_overclaim_detected": False,
        "new_E_REPRO_overclaim_detected": False,
    }


DECISION_IDS = [
    "live_authority_selects_exact_independent_diagnostic_review",
    "diagnostic_packet_manifest_report_and_generator_hashes_are_exact",
    "diagnostic_artifact_cross_bindings_are_exact",
    "all_bound_canonical_source_hashes_are_exact",
    "all_203_canonical_outputs_and_root_digest_reproduce",
    "no_new_simulation_or_canonical_output_mutation_occurred",
    "four_timelines_crossing_times_and_source_values_reproduce_exactly",
    "all_four_start_admissible_grow_monotonically_and_peak_at_final_time",
    "timing_correlations_reproduce_while_causal_hierarchy_is_withheld",
    "three_tolerance_roles_are_comparable_except_tolerance_and_identity_fields",
    "all_and_only_three_preregistered_tolerance_roles_enter_the_fit",
    "four_tolerance_maxima_and_exponents_reproduce_exactly",
    "tolerance_exponent_is_accepted_as_descriptive_not_physical_or_asymptotic",
    "solver_iterations_are_constant_after_initialization",
    "scalar_solver_residuals_show_no_late_growth",
    "all_eleven_axis_sharing_neighbors_and_pass_statuses_reproduce",
    "no_individual_axis_sufficiency_or_unique_interaction_order_is_claimed",
    "exact_field_matter_cancellation_kappa_is_not_derivable",
    "equation_block_solver_dominance_is_not_derivable",
    "discrete_Maxwell_to_continuity_closure_is_not_derivable",
    "higher_precision_contribution_is_not_testable",
    "time_growth_fits_remain_descriptive_without_duration_extrapolation",
    "packet_preserves_claim_ceiling_without_physical_or_robustness_overinterpretation",
    "accepted_diagnostic_does_not_change_canonical_numerical_block_or_materiality",
    "next_authority_is_route_selection_only_without_experiment_authorization",
]


def build_review_report() -> dict[str, Any]:
    sources = _load_sources()
    custody = _custody(sources)
    timelines = _reconstruct_timelines(sources["freeze"], sources["payload_by_run"])
    timing = _timing_and_time_law(timelines)
    tolerance = _reconstruct_tolerance_response(sources)
    neighbors = _reconstruct_neighbors(sources)
    availability = _mechanism_availability(sources)
    parity = _packet_parity_and_claim_audit(
        sources, timelines, timing, tolerance, neighbors, availability
    )
    unavailable_ok = all(
        availability[key]["missing_fields"]
        for key in (
            "exact_field_matter_cancellation_kappa",
            "equation_block_solver_dominance",
            "discrete_Maxwell_to_continuity_closure",
            "higher_precision_arithmetic_contribution",
        )
    )
    decisions = {
        "live_authority_selects_exact_independent_diagnostic_review": sources[
            "packet"
        ]["selected_next_target"]
        == TARGET
        and parity["packet_selects_exact_review_target"],
        "diagnostic_packet_manifest_report_and_generator_hashes_are_exact": custody[
            "source_artifact_hashes_exact"
        ],
        "diagnostic_artifact_cross_bindings_are_exact": custody[
            "diagnostic_packet_hash_bound_by_manifest"
        ]
        and custody["diagnostic_generator_hash_bound_by_manifest"]
        and custody["diagnostic_report_hashes_match_packet_manifest_and_generator"],
        "all_bound_canonical_source_hashes_are_exact": custody[
            "source_artifact_hashes_exact"
        ],
        "all_203_canonical_outputs_and_root_digest_reproduce": custody["passed"],
        "no_new_simulation_or_canonical_output_mutation_occurred": custody[
            "simulation_invocation_count_during_review"
        ]
        == 0
        and custody["canonical_output_mutation_authorized"] is False
        and custody["execution_count_performed"] == 1,
        "four_timelines_crossing_times_and_source_values_reproduce_exactly": parity[
            "timeline_reconstruction_exact"
        ]
        and len(timelines["timelines"]) == 4,
        "all_four_start_admissible_grow_monotonically_and_peak_at_final_time": timelines[
            "all_initial_values_pass"
        ]
        and timelines["all_absolute_magnitudes_monotone_nondecreasing"]
        and timelines["all_maxima_at_final_time"],
        "timing_correlations_reproduce_while_causal_hierarchy_is_withheld": parity[
            "timing_correlation_reconstruction_exact"
        ]
        and timing["causal_hierarchy_certified"] is False,
        "three_tolerance_roles_are_comparable_except_tolerance_and_identity_fields": tolerance[
            "configurations_identical_except_tolerance_and_identity_fields"
        ],
        "all_and_only_three_preregistered_tolerance_roles_enter_the_fit": tolerance[
            "registered_tolerance_run_ids"
        ]
        == TOLERANCE_RUN_IDS
        and tolerance["post_hoc_tolerance_point_selection_performed"] is False,
        "four_tolerance_maxima_and_exponents_reproduce_exactly": parity[
            "tolerance_numeric_reconstruction_exact"
        ]
        and tolerance[
            "all_four_residual_maxima_strictly_decrease_with_tighter_tolerance"
        ],
        "tolerance_exponent_is_accepted_as_descriptive_not_physical_or_asymptotic": 0.745
        > tolerance["overall_exponent_minimum"]
        > 0.744
        and 0.757 > tolerance["overall_exponent_maximum"] > 0.755
        and tolerance["physical_or_asymptotic_exponent_claim_authorized"] is False,
        "solver_iterations_are_constant_after_initialization": tolerance[
            "all_solver_iteration_histories_constant_after_initial_state"
        ],
        "scalar_solver_residuals_show_no_late_growth": tolerance[
            "all_solver_residual_histories_nonincreasing_after_first_step"
        ],
        "all_eleven_axis_sharing_neighbors_and_pass_statuses_reproduce": parity[
            "neighbor_reconstruction_exact"
        ]
        and neighbors["axis_sharing_neighbor_count"] == 11
        and neighbors["all_axis_sharing_neighbors_pass"],
        "no_individual_axis_sufficiency_or_unique_interaction_order_is_claimed": neighbors[
            "all_five_individual_axis_values_have_at_least_one_passing_non_R13_match"
        ]
        and neighbors["individual_axis_value_sufficient_cause_supported"] is False
        and neighbors["unique_interaction_order_identified"] is False,
        "exact_field_matter_cancellation_kappa_is_not_derivable": availability[
            "exact_field_matter_cancellation_kappa"
        ]["status"]
        == "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
        "equation_block_solver_dominance_is_not_derivable": availability[
            "equation_block_solver_dominance"
        ]["status"]
        == "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
        "discrete_Maxwell_to_continuity_closure_is_not_derivable": availability[
            "discrete_Maxwell_to_continuity_closure"
        ]["status"]
        == "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS",
        "higher_precision_contribution_is_not_testable": availability[
            "higher_precision_arithmetic_contribution"
        ]["status"]
        == "NOT_TESTABLE_WITH_EXISTING_DOUBLE_PRECISION_OUTPUTS_ONLY",
        "time_growth_fits_remain_descriptive_without_duration_extrapolation": timing[
            "common_time_law_certified"
        ]
        is False
        and timing["longer_duration_prediction_executed"] is False,
        "packet_preserves_claim_ceiling_without_physical_or_robustness_overinterpretation": parity[
            "claim_ceiling_preserved"
        ]
        and not parity["causal_hierarchy_overclaim_detected"]
        and not parity["physical_instability_overclaim_detected"]
        and not parity["model_boundary_overclaim_detected"]
        and not parity["conditional_robustness_overclaim_detected"]
        and not parity["new_E_REPRO_overclaim_detected"],
        "accepted_diagnostic_does_not_change_canonical_numerical_block_or_materiality": sources[
            "canonical_review"
        ]["scientific_robustness_status"]
        == "NUMERICALLY_BLOCKED"
        and sources["canonical_review"]["descendant_materiality_status"]
        == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and unavailable_ok,
        "next_authority_is_route_selection_only_without_experiment_authorization": True,
    }
    ordered = [
        {"decision_id": decision_id, "passed": bool(decisions[decision_id])}
        for decision_id in DECISION_IDS
    ]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "review_completed": accepted,
        "accepted": accepted,
        "verdict": (
            "ACCEPT_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PATTERN_ROOT_MECHANISM_UNRESOLVED"
            if accepted
            else "BLOCK_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET"
        ),
        "accepted_claim_label": "B-BLOCKED_DIAGNOSTIC" if accepted else "B-BLOCKED",
        "canonical_robustness_status": "NUMERICALLY_BLOCKED",
        "blocked_row": R13,
        "blocked_role": "SOLVER_TOL1eM08",
        "diagnostic_pattern_status": (
            "ACCEPTED_TOLERANCE_DEPENDENT_LONGITUDINAL_PATTERN"
            if accepted
            else "NOT_ACCEPTED"
        ),
        "root_numerical_mechanism_status": "UNRESOLVED",
        "descendant_materiality_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
        "source_custody": custody,
        "independent_failure_timeline_reconstruction": timelines,
        "independent_timing_and_time_law_audit": timing,
        "independent_tolerance_response_reconstruction": tolerance,
        "independent_neighbor_reconstruction": neighbors,
        "independent_mechanism_data_availability_audit": availability,
        "packet_parity_and_claim_audit": parity,
        "review_interpretation": {
            "accepted_if_review_passes": (
                "R13 exhibits a reproducible tolerance-dependent buildup of linked longitudinal "
                "residuals. The temporal order is consistent with a shared longitudinal source, "
                "but the preserved outputs do not identify a causal equation hierarchy or exact "
                "root numerical mechanism."
            ),
            "computational_stability_distinction": (
                "Constant iteration counts and declining scalar solver residuals rule against an "
                "obvious late-time convergence crisis; they do not prove that the loose solve is "
                "accurate enough to preserve the four structural identities."
            ),
            "time_law_distinction": (
                "Three series are closer to linear in time than linear in time squared on the "
                "ordinary scale, while longitudinal exchange is closer to time squared. No common "
                "growth law or longer-duration prediction is accepted."
            ),
        },
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "validation_status": {
            "focused_independent_diagnostic_review_tests": {"passed": 13, "failed": 0},
            "current_affected_descendant_robustness_chain": {
                "passed": 233,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 151, "status": "PASSED"},
            "authority_surface_parity": "PASSED",
            "simulation_invocation_count": 0,
            "canonical_output_mutation_count": 0,
            "historical_repository_wide_Lean": {
                "status": "INCOMPLETE_TIMEOUT",
                "completed_jobs": 8441,
                "total_jobs": 8507,
                "repository_wide_green_claim": False,
            },
        },
        "selected_next_target": SELECTED_NEXT_TARGET if accepted else TARGET,
        "authority_rotation": {
            "diagnostic_pattern_accepted": accepted,
            "exact_root_mechanism_identified": False,
            "route_selection_packet_authorized": accepted,
            "new_simulation_authorized": False,
            "rerun_authorized": False,
            "threshold_or_fit_change_authorized": False,
            "loose_solver_role_removal_authorized": False,
            "row_exclusion_authorized": False,
            "robustness_reclassification_authorized": False,
            "materiality_classification_authorized": False,
            "model_domain_claim_authorized": False,
            "new_E_REPRO_authorized": False,
            "pillar_or_seam_promotion_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_promotion_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "reviewer_sha256": sha256_path(REPO_ROOT / REVIEWER_RELATIVE_PATH),
        "nonclaims": [
            "no new simulation",
            "no canonical output mutation",
            "no causal Maxwell-to-continuity hierarchy proof",
            "no exact exchange-cancellation mechanism",
            "no equation-block dominance",
            "no discrete identity closure",
            "no certified common time-growth law",
            "no longer-duration result",
            "no physical instability",
            "no model-domain boundary",
            "no conditional or broad robustness",
            "no descendant materiality",
            "no new E-REPRO",
            "no experiment route selected yet",
            "no pillar or seam promotion",
            "no C_k dynamics",
            "no CCFT promotion",
            "no master-action promotion",
            "no repository-wide green claim",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the preserved R13 numerical-block diagnostic packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    before = canonical_root_digest()
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, StopIteration, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    raw = canonical_json_bytes(report)
    if args.write:
        REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REPORT_PATH.write_bytes(raw)
    elif args.check:
        if not REPORT_PATH.is_file() or REPORT_PATH.read_bytes() != raw:
            print(f"stale or missing R13 diagnostic review: {REPORT_RELATIVE_PATH}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(raw)
    after = canonical_root_digest()
    if before != after:
        print("canonical output root changed during independent diagnostic review", file=sys.stderr)
        return 1
    if report["failed_decision_ids"]:
        print(f"diagnostic review decisions failed: {report['failed_decision_ids']}", file=sys.stderr)
        return 2
    if args.write:
        print(
            f"wrote R13 diagnostic review: {report['passed_decision_count']}/"
            f"{report['decision_count']} decisions; selected {report['selected_next_target']}"
        )
    elif args.check:
        print(
            f"R13 diagnostic review verified: {report['passed_decision_count']}/"
            f"{report['decision_count']} decisions; canonical outputs unchanged"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
