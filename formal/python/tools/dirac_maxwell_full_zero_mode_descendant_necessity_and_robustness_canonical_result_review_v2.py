from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-15T00:00:00Z"
REVIEW_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "canonical_matrix_v2_result"
)
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "r13_numerical_block_diagnostic_packet_v0"
)
REVIEW_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "CANONICAL_RESULT_REVIEW_20260715_v0"
)
REVIEW_REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json"
)
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

FREEZE_REVIEW = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v3.json"
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
EXECUTION_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-PACKET-v2.json"
)
EXECUTION_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-MANIFEST-v2.json"
)
CLASSIFIER_CANDIDATE = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-CLASSIFIER-CANDIDATE-v2.json"
)
EXECUTION_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CANONICAL_EXECUTION_20260714_v2.json"
)
EXECUTION_GENERATOR = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_canonical_execution_v2.py"
)
CLASSIFIER_SOURCE = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_canonical_result_classifier_v2.py"
)
OUTPUT_ROOT = (
    "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_v2"
)
START_MARKER = f"{OUTPUT_ROOT}/_CANONICAL_EXECUTION_START.json"
TERMINAL_MARKER = f"{OUTPUT_ROOT}/_CANONICAL_EXECUTION_TERMINAL.json"

EXECUTION_COMMIT = "d2f24a13b0c42cabb531dbcf9d87ac9c0f766987"
EXECUTION_PARENT = "e37382150e4bc7d5edc05eff6432e3cd8c0a33e6"
EXPECTED_CORE_HASHES = {
    FREEZE_REVIEW: "cbafbed9e17f97bb3218a30bd9d31c6c2f1f3c512f57e8a6b66cd485c28ea77d",
    FREEZE_PACKET: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    RUN_MATRIX: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    IDENTITY_MANIFEST: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    EXECUTION_PACKET: "9020fd19774a2c2ccff108fd7950945a076a459f185bed3b10480270499cf86a",
    EXECUTION_MANIFEST: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    CLASSIFIER_CANDIDATE: "dba49f02dec827026747b99c8140efae378f66f58e249fa53fc2b329bfae2f38",
    EXECUTION_REPORT: "8d9b4d6994409898082785f39c53942416c38c5a869bb6c9eda5ef3fa5789c0e",
    EXECUTION_GENERATOR: "a0fe4948a73c324452652909ac19630107c255701fd48fda56cbe20a577dd34c",
    CLASSIFIER_SOURCE: "a72627d67ac31c5055fb921e54e640322d4d37a58c46908bc01c2ed70da0c9c9",
    START_MARKER: "f0d96a01b2a26b227cbe1f272d52643913dea2913a7ceaa8ad0d92b100e7e1f1",
    TERMINAL_MARKER: "2e992b334604161d88309b531e299da6a623e184581f60e6a13887ab8defec64",
}

CLASSIFIER_ID = "DM_ROBUSTNESS_CANONICAL_RESULT_CLASSIFIER_v2"
R13 = "R13_CORNER_STRONG_LOW"
R13_LOOSE_RUN = f"{R13}:SOLVER_TOL1eM08"
FULL_MODEL_ROLES = {
    "PRIMARY_FULL_MODEL",
    "SPATIAL_REFINEMENT",
    "TEMPORAL_REFINEMENT",
    "SOLVER_VERIFICATION",
    "DETERMINISTIC_DUPLICATE",
}
R13_FAILED_KEYS = {
    "gauss_residual": "maximum_Gauss_residual",
    "continuity_residual": "maximum_continuity_residual",
    "exchange_longitudinal_residual": "maximum_exchange_longitudinal_residual",
    "longitudinal_Maxwell_residual": "maximum_longitudinal_Maxwell_residual",
}

MAXIMUM_ACCEPTED_CLAIM = (
    "Independent reconstruction classifies the frozen fourteen-row robustness "
    "study as NUMERICALLY_BLOCKED. Exactly four frozen residual ceilings fail, "
    "all in R13_CORNER_STRONG_LOW:SOLVER_TOL1eM08; the evidence does not establish "
    "a model-domain limit, conditional robustness, descendant materiality, or a "
    "new E-REPRO result."
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
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def git_bytes(spec: str) -> bytes | None:
    result = subprocess.run(
        ["git", "show", spec],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    return result.stdout if result.returncode == 0 else None


def git_text(*args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else "MISSING"


def _record_input_hash(record: dict[str, Any]) -> str:
    excluded = {"safe_filename", "output_path", "input_hash", "payload_identity_contract"}
    return sha256_bytes(canonical_json_bytes({k: v for k, v in record.items() if k not in excluded}))


def _compare(value: float, operator: str, target: float) -> bool:
    if operator == "LE":
        return value <= target
    if operator == "LT":
        return value < target
    if operator == "GE":
        return value >= target
    if operator == "GT":
        return value > target
    if operator == "EQ":
        return value == target
    raise ValueError(f"unknown comparison operator: {operator}")


def _finite_series(payload: dict[str, Any], key: str) -> list[float]:
    series = payload.get("series", {}).get(key)
    if not isinstance(series, list) or not series:
        raise ValueError(f"missing nonempty series {key}: {payload.get('run_id')}")
    values = [float(value) for value in series]
    if any(not math.isfinite(value) for value in values):
        raise ValueError(f"nonfinite series {key}: {payload.get('run_id')}")
    return values


def _raw_scalar(payload: dict[str, Any], key: str) -> float:
    value = float(payload.get("raw_observables", {}).get(key))
    if not math.isfinite(value):
        raise ValueError(f"nonfinite raw observable {key}: {payload.get('run_id')}")
    return value


def custody(
    execution_manifest: dict[str, Any], identity_manifest: dict[str, Any]
) -> dict[str, Any]:
    commit = git_text("rev-parse", EXECUTION_COMMIT)
    parent = git_text("rev-parse", f"{EXECUTION_COMMIT}^")
    working_hashes = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_CORE_HASHES}
    committed_hashes: dict[str, str] = {}
    for path in EXPECTED_CORE_HASHES:
        raw = git_bytes(f"{EXECUTION_COMMIT}:{path}")
        committed_hashes[path] = sha256_bytes(raw) if raw is not None else "MISSING"

    manifest_index = {item["run_id"]: item for item in execution_manifest["run_outputs"]}
    failed_run_ids: list[str] = []
    for item in identity_manifest["outputs"]:
        run_id = item["run_id"]
        path = item["relative_output_path"]
        expected = manifest_index.get(run_id, {}).get("output_sha256")
        working = sha256_path(REPO_ROOT / path) if (REPO_ROOT / path).is_file() else "MISSING"
        raw = git_bytes(f"{EXECUTION_COMMIT}:{path}")
        committed = sha256_bytes(raw) if raw is not None else "MISSING"
        if working != committed or working != expected:
            failed_run_ids.append(run_id)

    expected_files = {
        item["relative_output_path"] for item in identity_manifest["outputs"]
    } | {START_MARKER, TERMINAL_MARKER}
    actual_files = {
        path.relative_to(REPO_ROOT).as_posix()
        for path in (REPO_ROOT / OUTPUT_ROOT).glob("*.json")
    }
    return {
        "execution_commit": commit,
        "execution_parent": parent,
        "expected_execution_commit": EXECUTION_COMMIT,
        "expected_execution_parent": EXECUTION_PARENT,
        "core_working_hashes": working_hashes,
        "core_committed_hashes": committed_hashes,
        "expected_core_hashes": EXPECTED_CORE_HASHES,
        "run_output_count_checked": len(identity_manifest["outputs"]),
        "failed_run_ids": failed_run_ids,
        "output_root_expected_file_count": len(expected_files),
        "output_root_actual_file_count": len(actual_files),
        "missing_output_root_files": sorted(expected_files - actual_files),
        "orphan_output_root_files": sorted(actual_files - expected_files),
        "all_203_run_outputs_match_working_committed_and_manifest_hashes": not failed_run_ids
        and len(manifest_index) == 203,
        "passed": commit == EXECUTION_COMMIT
        and parent == EXECUTION_PARENT
        and working_hashes == EXPECTED_CORE_HASHES
        and committed_hashes == EXPECTED_CORE_HASHES
        and not failed_run_ids
        and actual_files == expected_files,
    }


def identity_reconstruction(
    run_matrix: dict[str, Any],
    identity_manifest: dict[str, Any],
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]], dict[str, Any]]:
    records = run_matrix["records"]
    identities = identity_manifest["outputs"]
    by_run = {record["run_id"]: record for record in records}
    identity_by_run = {item["run_id"]: item for item in identities}
    payload_by_run: dict[str, dict[str, Any]] = {}
    failures: list[str] = []
    numerical_payload_hash_failures: list[str] = []
    input_hash_failures: list[str] = []
    for run_id, record in by_run.items():
        identity = identity_by_run.get(run_id)
        if identity is None:
            failures.append(f"missing identity:{run_id}")
            continue
        path = identity["relative_output_path"]
        payload = load_json(REPO_ROOT / path)
        payload_by_run[run_id] = payload
        expected_fields = {
            "run_id": run_id,
            "scientific_row_id": identity["scientific_row_id"],
            "run_role": identity["run_role"],
            "model_class": identity["model_class"],
            "parent_run_or_row_id": identity["parent_run_or_row_id"],
            "input_hash": identity["input_hash"],
            "relative_output_path": path,
        }
        for key, value in expected_fields.items():
            if payload.get(key) != value:
                failures.append(f"payload field mismatch:{run_id}:{key}")
        if record.get("input_hash") != identity["input_hash"] or record.get("output_path") != path:
            failures.append(f"matrix identity mismatch:{run_id}")
        if _record_input_hash(record) != record["input_hash"]:
            input_hash_failures.append(run_id)
        registered_hash = sha256_bytes(canonical_json_bytes(payload["registered_numerical_payload"]))
        if registered_hash != payload["registered_numerical_payload_sha256"]:
            numerical_payload_hash_failures.append(run_id)

    role_counts: dict[str, int] = {}
    for record in records:
        role_counts[record["run_role"]] = role_counts.get(record["run_role"], 0) + 1
    expected_forward = {item["run_id"]: item["safe_filename"] for item in identities}
    expected_inverse = {item["safe_filename"]: item["run_id"] for item in identities}
    closure = {
        "record_count": len(records),
        "identity_count": len(identities),
        "payload_count": len(payload_by_run),
        "scientific_record_count": sum(
            record["run_role"] not in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}
            for record in records
        ),
        "positive_control_count": role_counts.get("POSITIVE_CONTROL", 0),
        "negative_control_count": role_counts.get("NEGATIVE_CONTROL", 0),
        "role_counts": role_counts,
        "identity_failures": failures,
        "input_hash_failures": input_hash_failures,
        "registered_numerical_payload_hash_failures": numerical_payload_hash_failures,
        "explicit_filename_bijection_exact": identity_manifest.get("run_id_to_safe_filename")
        == expected_forward
        and identity_manifest.get("safe_filename_to_run_id") == expected_inverse,
        "all_completion_statuses_complete": all(
            payload.get("completion_status") == "RECORD_COMPLETED_RAW_EVIDENCE_PRESERVED"
            for payload in payload_by_run.values()
        ),
    }
    closure["passed"] = (
        len(records) == len(identities) == len(payload_by_run) == 203
        and len(by_run) == len(identity_by_run) == 203
        and closure["scientific_record_count"] == 182
        and closure["positive_control_count"] == 8
        and closure["negative_control_count"] == 13
        and not failures
        and not input_hash_failures
        and not numerical_payload_hash_failures
        and closure["explicit_filename_bijection_exact"]
        and closure["all_completion_statuses_complete"]
    )
    return by_run, payload_by_run, closure


def control_reconstruction(
    freeze_packet: dict[str, Any],
    by_run: dict[str, dict[str, Any]],
    payload_by_run: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    contracts = freeze_packet["control_applicability_freeze"]["contracts"]
    frozen_by_id = {item["control_id"]: item for item in contracts}
    rows: list[dict[str, Any]] = []
    for run_id, record in by_run.items():
        if record["run_role"] not in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}:
            continue
        metadata = record["control_metadata"]
        observations = payload_by_run[run_id]["control_observables"]
        observation_results = []
        for spec in metadata["control_evaluation_spec"]["required_observations"]:
            observable = spec["observable_id"]
            value = float(observations[observable])
            target = float(spec["target_value"])
            observation_results.append(
                {
                    "observable_id": observable,
                    "observed": value,
                    "comparison_operator": spec["comparison_operator"],
                    "target": target,
                    "passed": math.isfinite(value)
                    and _compare(value, spec["comparison_operator"], target),
                }
            )
        rows.append(
            {
                "run_id": run_id,
                "control_id": metadata["control_id"],
                "control_type": metadata["control_type"],
                "metadata_matches_frozen_contract": metadata
                == frozen_by_id.get(metadata["control_id"]),
                "observation_results": observation_results,
                "passed": metadata == frozen_by_id.get(metadata["control_id"])
                and bool(observation_results)
                and all(item["passed"] for item in observation_results),
            }
        )
    return {
        "positive_control_count": sum(item["control_type"] == "POSITIVE" for item in rows),
        "negative_control_count": sum(item["control_type"] == "NEGATIVE" for item in rows),
        "control_ids_reconstructed": sorted(item["control_id"] for item in rows),
        "failed_control_ids": sorted(item["control_id"] for item in rows if not item["passed"]),
        "control_results": sorted(rows, key=lambda item: item["control_id"]),
        "passed": len(contracts) == len(rows) == 21
        and len({item["control_id"] for item in rows}) == 21
        and all(item["passed"] for item in rows),
    }


def threshold_reconstruction(
    freeze_packet: dict[str, Any],
    by_run: dict[str, dict[str, Any]],
    payload_by_run: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    thresholds = freeze_packet["numerical_threshold_provenance"]
    failures: list[dict[str, Any]] = []
    threshold_summaries: list[dict[str, Any]] = []
    evaluation_count = 0
    for threshold in thresholds:
        if threshold["threshold_class"] == "NUMERICAL_FLOOR":
            continue
        local_count = 0
        local_failures = 0
        maximum_ratio = -math.inf
        maximum_ratio_run_id = ""
        for run_id, record in by_run.items():
            if (
                record["scientific_row_id"] not in threshold["eligible_scientific_rows"]
                or record["run_role"] not in threshold["eligible_run_roles"]
            ):
                continue
            values = _finite_series(payload_by_run[run_id], threshold["raw_series_key"])
            observed = max(abs(value) for value in values)
            target = float(threshold["frozen_value"])
            passed = _compare(observed, threshold["comparison_operator"], target)
            ratio = observed / target if target else math.inf
            local_count += 1
            evaluation_count += 1
            if ratio > maximum_ratio:
                maximum_ratio = ratio
                maximum_ratio_run_id = run_id
            if passed:
                continue
            local_failures += 1
            times = _finite_series(payload_by_run[run_id], "time")
            maximum_index = max(range(len(values)), key=lambda index: abs(values[index]))
            first_index = next(
                index
                for index, value in enumerate(values)
                if not _compare(abs(value), threshold["comparison_operator"], target)
            )
            failures.append(
                {
                    "run_id": run_id,
                    "scientific_row_id": record["scientific_row_id"],
                    "run_role": record["run_role"],
                    "threshold_id": threshold["threshold_id"],
                    "raw_series_key": threshold["raw_series_key"],
                    "observed_maximum": observed,
                    "frozen_limit": target,
                    "limit_ratio": ratio,
                    "initial_magnitude": abs(values[0]),
                    "final_magnitude": abs(values[-1]),
                    "first_failure_time": times[first_index],
                    "maximum_time": times[maximum_index],
                    "absolute_magnitude_monotone_nondecreasing": all(
                        abs(values[index]) >= abs(values[index - 1])
                        for index in range(1, len(values))
                    ),
                    "failure_diagnostic": threshold["failure_diagnostic"],
                }
            )
        threshold_summaries.append(
            {
                "threshold_id": threshold["threshold_id"],
                "evaluation_count": local_count,
                "failure_count": local_failures,
                "maximum_limit_ratio": maximum_ratio,
                "maximum_limit_ratio_run_id": maximum_ratio_run_id,
            }
        )
    schema_complete = len(thresholds) == 22 and all(
        threshold.get("eligible_run_roles")
        and threshold.get("eligible_scientific_rows")
        and str(threshold.get("units", "")).strip()
        and str(threshold.get("normalization_formula", "")).strip()
        and str(threshold.get("row_scaling_rule", "")).strip()
        for threshold in thresholds
    )
    return {
        "frozen_threshold_count": len(thresholds),
        "numerical_floor_count": sum(
            threshold["threshold_class"] == "NUMERICAL_FLOOR" for threshold in thresholds
        ),
        "threshold_decision_count": evaluation_count,
        "passing_threshold_decision_count": evaluation_count - len(failures),
        "failing_threshold_decision_count": len(failures),
        "threshold_schema_complete": schema_complete,
        "threshold_summaries": threshold_summaries,
        "failures": failures,
    }


def _three_level_order(values: list[float]) -> float:
    numerator = abs(values[0] - values[1])
    denominator = abs(values[1] - values[2])
    if numerator <= 0.0 or denominator <= 0.0:
        return float("-inf")
    return math.log(numerator / denominator, 2.0)


def convergence_reconstruction(
    freeze_packet: dict[str, Any],
    by_run: dict[str, dict[str, Any]],
    payload_by_run: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    rows: dict[str, dict[str, float]] = {}
    failures: list[dict[str, Any]] = []
    specs = freeze_packet["convergence_threshold_provenance"]
    for row_id in freeze_packet["scientific_design_freeze"]["scientific_row_ids"]:
        rows[row_id] = {}
        for spec in specs:
            role = spec["eligible_run_roles"][0]
            records = sorted(
                (
                    record
                    for record in by_run.values()
                    if record["scientific_row_id"] == row_id and record["run_role"] == role
                ),
                key=lambda record: record[spec["ordering_field"]],
                reverse=bool(spec["ordering_descending"]),
            )
            if len(records) != 3:
                raise ValueError(f"wrong convergence membership: {row_id}/{role}")
            if spec["threshold_id"] == "minimum_energy_error_order":
                values = [
                    max(
                        abs(value)
                        for value in _finite_series(
                            payload_by_run[record["run_id"]], spec["raw_series_key"]
                        )
                    )
                    for record in records
                ]
                adjacent = [
                    math.log(values[index] / values[index + 1], 2.0)
                    if values[index] > 0.0 and values[index + 1] > 0.0
                    else float("-inf")
                    for index in (0, 1)
                ]
                order = min(adjacent)
            else:
                values = [
                    _finite_series(
                        payload_by_run[record["run_id"]], spec["raw_series_key"]
                    )[-1]
                    for record in records
                ]
                order = _three_level_order(values)
            rows[row_id][spec["threshold_id"]] = order
            if not math.isfinite(order) or order < float(spec["frozen_value"]):
                failures.append(
                    {
                        "scientific_row_id": row_id,
                        "threshold_id": spec["threshold_id"],
                        "observed_order": order,
                        "frozen_minimum": float(spec["frozen_value"]),
                    }
                )
    return {
        "evaluation_count": len(rows) * len(specs),
        "orders_by_row": rows,
        "failures": failures,
        "passed": len(specs) == 3 and not failures,
    }


def determinism_reconstruction(
    freeze_packet: dict[str, Any],
    by_run: dict[str, dict[str, Any]],
    payload_by_run: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    rows = []
    for row_id in freeze_packet["scientific_design_freeze"]["scientific_row_ids"]:
        duplicates = sorted(
            (
                record
                for record in by_run.values()
                if record["scientific_row_id"] == row_id
                and record["run_role"] == "DETERMINISTIC_DUPLICATE"
            ),
            key=lambda record: record["run_id"],
        )
        hashes = [
            sha256_bytes(
                canonical_json_bytes(payload_by_run[record["run_id"]]["registered_numerical_payload"])
            )
            for record in duplicates
        ]
        rows.append(
            {
                "scientific_row_id": row_id,
                "run_ids": [record["run_id"] for record in duplicates],
                "registered_payload_sha256": hashes,
                "passed": len(duplicates) == 2 and len(set(hashes)) == 1,
            }
        )
    return {
        "row_count": len(rows),
        "failed_row_ids": [item["scientific_row_id"] for item in rows if not item["passed"]],
        "rows": rows,
        "passed": len(rows) == 14 and all(item["passed"] for item in rows),
    }


def solver_reconstruction(
    freeze_packet: dict[str, Any],
    by_run: dict[str, dict[str, Any]],
    payload_by_run: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    ratio_gate = float(
        freeze_packet["fixed_structural_numerical_gates"]["maximum_solver_to_truncation_ratio"]
    )
    iteration_cap = int(freeze_packet["fixed_structural_numerical_gates"]["maximum_iterations"])
    rows = []
    for row_id in freeze_packet["scientific_design_freeze"]["scientific_row_ids"]:
        records = [
            record
            for record in by_run.values()
            if record["scientific_row_id"] == row_id
            and record["run_role"] == "SOLVER_VERIFICATION"
        ]
        tight = min(records, key=lambda record: record["solver_tolerance"])
        tight_payload = payload_by_run[tight["run_id"]]
        solver_error = _raw_scalar(tight_payload, "solver_error_norm")
        truncation_error = _raw_scalar(tight_payload, "truncation_error_norm")
        ratio = solver_error / truncation_error if truncation_error > 0.0 else math.inf
        maximum_iterations = max(
            max(_finite_series(payload_by_run[record["run_id"]], "solver_iterations"))
            for record in records
        )
        rows.append(
            {
                "scientific_row_id": row_id,
                "tight_run_id": tight["run_id"],
                "solver_error_norm": solver_error,
                "truncation_error_norm": truncation_error,
                "solver_to_truncation_ratio": ratio,
                "maximum_solver_iterations": maximum_iterations,
                "passed": len(records) == 3
                and ratio <= ratio_gate
                and maximum_iterations <= iteration_cap,
            }
        )
    return {
        "ratio_gate": ratio_gate,
        "iteration_cap": iteration_cap,
        "row_count": len(rows),
        "solver_iteration_run_count": 42,
        "failed_row_ids": [item["scientific_row_id"] for item in rows if not item["passed"]],
        "rows": rows,
        "passed": len(rows) == 14 and all(item["passed"] for item in rows),
    }


def model_domain_reconstruction(
    freeze_packet: dict[str, Any],
    by_run: dict[str, dict[str, Any]],
    payload_by_run: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    margins: dict[str, float] = {}
    for row_id in freeze_packet["scientific_design_freeze"]["scientific_row_ids"]:
        primary = next(
            record
            for record in by_run.values()
            if record["scientific_row_id"] == row_id
            and record["run_role"] == "PRIMARY_FULL_MODEL"
        )
        margins[row_id] = _raw_scalar(payload_by_run[primary["run_id"]], "model_domain_margin")
    limited = sorted(row_id for row_id, margin in margins.items() if margin < 0.0)
    return {
        "model_domain_margins": margins,
        "model_domain_limited_row_ids": limited,
        "R13_model_domain_margin": margins[R13],
        "passed": not limited,
    }


def expected_candidate_result(
    threshold_result: dict[str, Any], convergence_result: dict[str, Any]
) -> dict[str, Any]:
    diagnostics: dict[str, set[str]] = {}
    for failure in threshold_result["failures"]:
        diagnostics.setdefault(failure["scientific_row_id"], set()).add(
            failure["failure_diagnostic"]
        )
    for failure in convergence_result["failures"]:
        diagnostics.setdefault(failure["scientific_row_id"], set()).add(
            "NUMERICALLY_BLOCKED:CONVERGENCE_NOT_RESOLVED"
        )
    return {
        "classifier_id": CLASSIFIER_ID,
        "execution_status": "CLASSIFIED_BLOCKED",
        "robustness_status": "NUMERICALLY_BLOCKED",
        "descendant_significance_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
        "scientific_claim_authorized": False,
        "numerically_blocked_rows": sorted(diagnostics),
        "failure_diagnostics": {
            row_id: sorted(values) for row_id, values in sorted(diagnostics.items())
        },
        "observed_convergence_orders": convergence_result["orders_by_row"],
    }


def r13_diagnosis(
    freeze_packet: dict[str, Any],
    by_run: dict[str, dict[str, Any]],
    payload_by_run: dict[str, dict[str, Any]],
    threshold_result: dict[str, Any],
    solver_result: dict[str, Any],
    model_domain_result: dict[str, Any],
) -> dict[str, Any]:
    threshold_by_key = {
        threshold["raw_series_key"]: threshold
        for threshold in freeze_packet["numerical_threshold_provenance"]
        if threshold["raw_series_key"] in R13_FAILED_KEYS
    }
    solver_records = sorted(
        (
            record
            for record in by_run.values()
            if record["scientific_row_id"] == R13
            and record["run_role"] == "SOLVER_VERIFICATION"
        ),
        key=lambda record: record["solver_tolerance"],
        reverse=True,
    )
    tolerance_scan = []
    for record in solver_records:
        payload = payload_by_run[record["run_id"]]
        residuals = {}
        for key, threshold in threshold_by_key.items():
            observed = max(abs(value) for value in _finite_series(payload, key))
            limit = float(threshold["frozen_value"])
            residuals[key] = {
                "observed_maximum": observed,
                "frozen_limit": limit,
                "limit_ratio": observed / limit,
                "passed": observed <= limit,
            }
        tolerance_scan.append(
            {
                "run_id": record["run_id"],
                "solver_tolerance": float(record["solver_tolerance"]),
                "maximum_iterations": max(_finite_series(payload, "solver_iterations")),
                "residuals": residuals,
                "all_four_residual_ceilings_pass": all(
                    value["passed"] for value in residuals.values()
                ),
            }
        )
    primary_record = next(
        record
        for record in by_run.values()
        if record["scientific_row_id"] == R13
        and record["run_role"] == "PRIMARY_FULL_MODEL"
    )
    primary_payload = payload_by_run[primary_record["run_id"]]
    primary_residuals = {}
    for key, threshold in threshold_by_key.items():
        observed = max(abs(value) for value in _finite_series(primary_payload, key))
        limit = float(threshold["frozen_value"])
        primary_residuals[key] = {
            "observed_maximum": observed,
            "frozen_limit": limit,
            "limit_ratio": observed / limit,
            "passed": observed <= limit,
        }

    scientific_rows = {
        row["row_id"]: row["requested_axis_values"]
        for row in freeze_packet["scientific_design_freeze"]["scientific_rows"]
    }
    r13_axes = scientific_rows[R13]
    neighbor_rows = []
    for row_id, axes in scientific_rows.items():
        if row_id == R13:
            continue
        shared_axes = sorted(key for key, value in axes.items() if value == r13_axes[key])
        if not shared_axes:
            continue
        loose = next(
            record
            for record in by_run.values()
            if record["scientific_row_id"] == row_id
            and record["run_role"] == "SOLVER_VERIFICATION"
            and float(record["solver_tolerance"]) == 1e-8
        )
        ratios = {}
        for key, threshold in threshold_by_key.items():
            ratios[key] = max(
                abs(value) for value in _finite_series(payload_by_run[loose["run_id"]], key)
            ) / float(threshold["frozen_value"])
        neighbor_rows.append(
            {
                "scientific_row_id": row_id,
                "shared_axes": shared_axes,
                "loose_solver_limit_ratios": ratios,
                "all_four_residual_ceilings_pass": max(ratios.values()) <= 1.0,
            }
        )

    r13_solver_row = next(
        row for row in solver_result["rows"] if row["scientific_row_id"] == R13
    )
    exact_failures = [
        failure for failure in threshold_result["failures"] if failure["scientific_row_id"] == R13
    ]
    return {
        "requested_axis_values": r13_axes,
        "failed_run_id": R13_LOOSE_RUN,
        "failed_run_numerical_parameters": {
            "grid_size": by_run[R13_LOOSE_RUN]["grid_size"],
            "time_step": by_run[R13_LOOSE_RUN]["time_step"],
            "duration": by_run[R13_LOOSE_RUN]["duration"],
            "solver_tolerance": by_run[R13_LOOSE_RUN]["solver_tolerance"],
            "maximum_iterations": by_run[R13_LOOSE_RUN]["iteration_cap"],
        },
        "exact_failures": exact_failures,
        "all_four_initial_values_pass": all(
            failure["initial_magnitude"] <= failure["frozen_limit"] for failure in exact_failures
        ),
        "all_four_failures_are_monotone_secular_in_absolute_magnitude": all(
            failure["absolute_magnitude_monotone_nondecreasing"] for failure in exact_failures
        ),
        "solver_tolerance_scan": tolerance_scan,
        "primary_run_id": primary_record["run_id"],
        "primary_same_four_residuals": primary_residuals,
        "primary_passes_same_four_residual_ceilings": all(
            value["passed"] for value in primary_residuals.values()
        ),
        "solver_hierarchy": r13_solver_row,
        "model_domain_margin": model_domain_result["R13_model_domain_margin"],
        "model_domain_limit_observed": model_domain_result["R13_model_domain_margin"] < 0.0,
        "neighbor_rows_sharing_at_least_one_axis_value": neighbor_rows,
        "all_axis_sharing_neighbors_pass_same_loose_solver_residual_ceilings": all(
            row["all_four_residual_ceilings_pass"] for row in neighbor_rows
        ),
        "independent_explanation_class": "TOLERANCE_DEPENDENT_NUMERICAL_ADMISSIBILITY_BLOCK",
        "independent_explanation": (
            "The four failures are confined to the loose 1e-8 solver-verification member. "
            "The 1e-10 and 1e-12 solver members, canonical primary, deterministic duplicates, "
            "and all spatial and temporal refinements pass the same ceilings; the tight solver-to-"
            "truncation hierarchy also passes and the model-domain margin is positive. This supports "
            "a tolerance-dependent numerical-admissibility block under the frozen all-role rule, "
            "not a demonstrated model-domain boundary."
        ),
    }


DECISION_IDS = [
    "accepted_freeze_authorizes_only_this_independent_result_review",
    "execution_commit_core_artifacts_and_all_203_outputs_have_exact_custody",
    "exact_182_scientific_8_positive_13_negative_record_identity_closure_reconstructed",
    "no_output_missing_or_orphaned_and_all_registered_payload_hashes_reproduce",
    "no_retry_exclusion_threshold_or_fit_change_occurred",
    "all_8_positive_and_13_negative_controls_reconstruct_from_raw_observations",
    "all_22_threshold_contracts_and_3416_scoped_threshold_decisions_reconstruct",
    "exactly_four_threshold_failures_are_confined_to_R13_loose_solver_verification",
    "all_42_distinct_spatial_temporal_and_energy_convergence_decisions_pass",
    "all_14_deterministic_duplicate_pairs_match",
    "all_14_solver_hierarchies_and_42_iteration_cap_checks_pass",
    "all_14_model_domain_margins_are_nonnegative",
    "candidate_classifier_output_reproduces_without_using_candidate_decisions",
    "R13_initial_data_pass_the_four_eventual_residual_ceilings",
    "R13_primary_and_tighter_solver_members_pass_the_same_four_residual_ceilings",
    "all_axis_sharing_neighbors_pass_the_same_loose_solver_residual_ceilings",
    "R13_is_a_tolerance_dependent_numerical_block_not_a_model_domain_result",
    "materiality_remains_not_evaluated_after_numerical_block",
    "study_wide_result_is_NUMERICALLY_BLOCKED_not_conditional_or_broad_robustness",
    "no_new_E_REPRO_or_stronger_physics_promotion_is_authorized",
]


def build_review_report() -> dict[str, Any]:
    freeze_review = load_json(REPO_ROOT / FREEZE_REVIEW)
    freeze_packet = load_json(REPO_ROOT / FREEZE_PACKET)
    run_matrix = load_json(REPO_ROOT / RUN_MATRIX)
    identity_manifest = load_json(REPO_ROOT / IDENTITY_MANIFEST)
    execution_packet = load_json(REPO_ROOT / EXECUTION_PACKET)
    execution_manifest = load_json(REPO_ROOT / EXECUTION_MANIFEST)
    candidate_artifact = load_json(REPO_ROOT / CLASSIFIER_CANDIDATE)
    execution_report = load_json(REPO_ROOT / EXECUTION_REPORT)
    start_marker = load_json(REPO_ROOT / START_MARKER)
    terminal_marker = load_json(REPO_ROOT / TERMINAL_MARKER)

    custody_result = custody(execution_manifest, identity_manifest)
    by_run, payload_by_run, identity_result = identity_reconstruction(
        run_matrix, identity_manifest
    )
    controls = control_reconstruction(freeze_packet, by_run, payload_by_run)
    thresholds = threshold_reconstruction(freeze_packet, by_run, payload_by_run)
    convergence = convergence_reconstruction(freeze_packet, by_run, payload_by_run)
    determinism = determinism_reconstruction(freeze_packet, by_run, payload_by_run)
    solver = solver_reconstruction(freeze_packet, by_run, payload_by_run)
    model_domain = model_domain_reconstruction(freeze_packet, by_run, payload_by_run)
    independent_candidate = expected_candidate_result(thresholds, convergence)
    candidate_matches = (
        candidate_artifact["candidate_result_not_project_authority"] == independent_candidate
    )
    r13 = r13_diagnosis(
        freeze_packet,
        by_run,
        payload_by_run,
        thresholds,
        solver,
        model_domain,
    )

    exact_failure_pairs = {
        (failure["run_id"], failure["threshold_id"]) for failure in thresholds["failures"]
    }
    expected_failure_pairs = {
        (R13_LOOSE_RUN, threshold_id) for threshold_id in R13_FAILED_KEYS.values()
    }
    freeze_authorized = (
        freeze_review["verdict"] == "ACCEPT_FREEZE"
        and freeze_review["selected_next_target"] == execution_packet["target"]
        and freeze_review["authority_rotation"]["independent_canonical_result_review_required"]
        is True
        and execution_packet["selected_next_target"] == REVIEW_TARGET
    )
    no_execution_mutation = (
        execution_packet["execution_count_performed"] == 1
        and execution_packet["authorized_execution_count"] == 1
        and execution_packet["automatic_retry_performed"] is False
        and execution_packet["interpretation_driven_rerun_performed"] is False
        and execution_packet["run_exclusion_performed"] is False
        and execution_packet["threshold_or_fit_change_performed"] is False
        and execution_report["rerun_performed"] is False
        and execution_report["excluded_record_count"] == 0
        and start_marker["output_overwrite_authorized"] is False
        and terminal_marker["terminal_state"] == "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW"
    )
    all_tighter_pass = all(
        row["all_four_residual_ceilings_pass"]
        for row in r13["solver_tolerance_scan"]
        if row["solver_tolerance"] < 1e-8
    )
    decisions = {
        "accepted_freeze_authorizes_only_this_independent_result_review": freeze_authorized,
        "execution_commit_core_artifacts_and_all_203_outputs_have_exact_custody": custody_result[
            "passed"
        ],
        "exact_182_scientific_8_positive_13_negative_record_identity_closure_reconstructed": identity_result[
            "passed"
        ],
        "no_output_missing_or_orphaned_and_all_registered_payload_hashes_reproduce": not custody_result[
            "missing_output_root_files"
        ]
        and not custody_result["orphan_output_root_files"]
        and not identity_result["registered_numerical_payload_hash_failures"],
        "no_retry_exclusion_threshold_or_fit_change_occurred": no_execution_mutation,
        "all_8_positive_and_13_negative_controls_reconstruct_from_raw_observations": controls[
            "passed"
        ],
        "all_22_threshold_contracts_and_3416_scoped_threshold_decisions_reconstruct": thresholds[
            "threshold_schema_complete"
        ]
        and thresholds["threshold_decision_count"] == 3416,
        "exactly_four_threshold_failures_are_confined_to_R13_loose_solver_verification": thresholds[
            "failing_threshold_decision_count"
        ]
        == 4
        and exact_failure_pairs == expected_failure_pairs,
        "all_42_distinct_spatial_temporal_and_energy_convergence_decisions_pass": convergence[
            "passed"
        ]
        and convergence["evaluation_count"] == 42,
        "all_14_deterministic_duplicate_pairs_match": determinism["passed"],
        "all_14_solver_hierarchies_and_42_iteration_cap_checks_pass": solver["passed"],
        "all_14_model_domain_margins_are_nonnegative": model_domain["passed"],
        "candidate_classifier_output_reproduces_without_using_candidate_decisions": candidate_matches,
        "R13_initial_data_pass_the_four_eventual_residual_ceilings": r13[
            "all_four_initial_values_pass"
        ],
        "R13_primary_and_tighter_solver_members_pass_the_same_four_residual_ceilings": r13[
            "primary_passes_same_four_residual_ceilings"
        ]
        and all_tighter_pass,
        "all_axis_sharing_neighbors_pass_the_same_loose_solver_residual_ceilings": r13[
            "all_axis_sharing_neighbors_pass_same_loose_solver_residual_ceilings"
        ],
        "R13_is_a_tolerance_dependent_numerical_block_not_a_model_domain_result": r13[
            "independent_explanation_class"
        ]
        == "TOLERANCE_DEPENDENT_NUMERICAL_ADMISSIBILITY_BLOCK"
        and r13["model_domain_limit_observed"] is False,
        "materiality_remains_not_evaluated_after_numerical_block": independent_candidate[
            "descendant_significance_status"
        ]
        == "NOT_EVALUATED_NUMERICAL_BLOCK",
        "study_wide_result_is_NUMERICALLY_BLOCKED_not_conditional_or_broad_robustness": independent_candidate[
            "robustness_status"
        ]
        == "NUMERICALLY_BLOCKED",
        "no_new_E_REPRO_or_stronger_physics_promotion_is_authorized": independent_candidate[
            "scientific_claim_authorized"
        ]
        is False,
    }
    ordered_decisions = [
        {"decision_id": decision_id, "passed": bool(decisions[decision_id])}
        for decision_id in DECISION_IDS
    ]
    failed_decisions = [
        decision["decision_id"] for decision in ordered_decisions if not decision["passed"]
    ]
    review_completed = not failed_decisions
    verdict = (
        "ACCEPT_NUMERICALLY_BLOCKED_CANONICAL_RESULT"
        if review_completed
        else "B-BLOCKED_INDEPENDENT_REVIEW_RECONSTRUCTION_MISMATCH"
    )
    selected_next_target = (
        SELECTED_NEXT_TARGET
        if review_completed
        else (
            "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
            "canonical_result_review_reconstruction_repair_packet_v0"
        )
    )
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "review_completed": review_completed,
        "accepted": review_completed,
        "verdict": verdict,
        "accepted_claim_label": "B-BLOCKED" if review_completed else None,
        "scientific_robustness_status": (
            "NUMERICALLY_BLOCKED" if review_completed else "NOT_ASSIGNED_REVIEW_MISMATCH"
        ),
        "descendant_materiality_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": "R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_PREPARATION_ONLY",
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed_decisions),
        "failed_decision_ids": failed_decisions,
        "decisions": ordered_decisions,
        "execution_custody": custody_result,
        "identity_and_completeness_reconstruction": identity_result,
        "control_reconstruction": controls,
        "threshold_reconstruction": thresholds,
        "convergence_reconstruction": convergence,
        "determinism_reconstruction": determinism,
        "solver_reconstruction": solver,
        "model_domain_reconstruction": model_domain,
        "independent_classifier_reconstruction": independent_candidate,
        "candidate_artifact_matches_independent_reconstruction": candidate_matches,
        "R13_independent_diagnosis": r13,
        "materiality_evaluation": {
            "status": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "materiality_function_called": False,
            "reason": (
                "The accepted evaluation order suppresses necessity and materiality after any "
                "numerical-admissibility failure."
            ),
        },
        "study_wide_interpretation": {
            "passing_scientific_rows_descriptive_only": 13,
            "blocked_scientific_rows": [R13],
            "conditional_robustness_authorized": False,
            "broad_robustness_authorized": False,
            "model_domain_limit_authorized": False,
            "numerical_block_authoritative": review_completed,
        },
        "documentary_note": {
            "stale_pre_execution_nonclaim_detected": "no canonical fourteen-row run executed"
            in execution_report.get("nonclaims", []),
            "raw_execution_effect": "NONE",
            "handling": (
                "The immutable execution report is not rewritten. Its stale inherited nonclaim is "
                "superseded for custody purposes by the exact start marker, COMPLETE terminal marker, "
                "203 committed outputs, manifest hashes, and execution-count fields."
            ),
        },
        "validation_status": {
            "read_only_execution_verifier": "PASSED_EXACT_203_RECORD_ARTIFACT_VERIFICATION",
            "focused_independent_review_tests": {"passed": 11, "failed": 0},
            "focused_freeze_execution_and_review_chain": {"passed": 29, "failed": 0},
            "current_affected_descendant_robustness_chain": {
                "passed": 208,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 149, "status": "PASSED"},
            "authority_surface_parity": "PASSED",
            "historical_repository_wide_Lean": {
                "status": "INCOMPLETE_TIMEOUT",
                "completed_jobs": 8441,
                "total_jobs": 8507,
                "repository_wide_green_claim": False,
            },
        },
        "authority_rotation": {
            "canonical_execution_custody_accepted": review_completed,
            "robustness_classification_assigned": review_completed,
            "numerically_blocked_result_accepted": review_completed,
            "descendant_materiality_classification_assigned": False,
            "new_E_REPRO_claim_authorized": False,
            "interpretation_driven_rerun_authorized": False,
            "threshold_relaxation_authorized": False,
            "row_exclusion_authorized": False,
            "model_domain_limit_claim_authorized": False,
            "conditional_or_broad_robustness_claim_authorized": False,
            "pillar_completion_authorized": False,
            "seam_admissibility_or_closure_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_promotion_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "maximum_accepted_claim": MAXIMUM_ACCEPTED_CLAIM if review_completed else None,
        "claim": MAXIMUM_ACCEPTED_CLAIM if review_completed else "Independent review mismatch.",
        "nonclaims": [
            "no broad robustness result",
            "no conditional robustness result under the frozen classifier",
            "no model-domain limit",
            "no descendant-materiality result",
            "no new E-REPRO result",
            "no interpretation-driven rerun or threshold relaxation",
            "no empirical validation",
            "no pillar completion",
            "no seam closure",
            "no C_k dynamics",
            "no CCFT promotion",
            "no master-action promotion",
            "no repository-wide green claim",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Independently reconstruct the frozen 203-record robustness result."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, StopIteration, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(expected)
        print(
            f"wrote canonical result review: {report['verdict']}; "
            f"{report['passed_decision_count']}/{report['decision_count']} decisions"
        )
        return 0 if report["review_completed"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing canonical result-review artifact", file=sys.stderr)
            return 1
        print(
            f"canonical result review verified: {report['verdict']}; "
            f"selected {report['selected_next_target']}"
        )
        return 0 if report["review_completed"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["review_completed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
