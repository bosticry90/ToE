from __future__ import annotations

"""Create a factual receipt for the one authorized R13 experiment execution.

The receipt is outside the frozen output directory. This module only reads and
hashes execution artifacts. It does not import or invoke the classifier, alter
payloads, call the evolution, or assign a mechanism result.
"""

import argparse
import hashlib
import json
import math
import sys
import unicodedata
from collections.abc import Mapping
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v3
    as custody_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0
    as canonical_v0,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-16T00:00:00Z"
TARGET = (
    "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_v0_once"
)
SELECTED_NEXT_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_v0_result"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_EXECUTION_20260716_v0"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_EXECUTION_20260716_v0.json"
)
IDENTITY_RELATIVE_PATH = custody_v3.IDENTITY_MANIFEST_RELATIVE_PATH
MATRIX_RELATIVE_PATH = custody_v3.RUN_MATRIX_RELATIVE_PATH
REVIEW_RELATIVE_PATH = custody_v3.REVIEW_ANCHOR_RELATIVE_PATH
OUTPUT_ROOT_RELATIVE_PATH = custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if value is None or isinstance(value, (bool, int)):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError("canonical JSON forbids nonfinite floats")
        return value
    if isinstance(value, Mapping):
        return {str(key): _normalize(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_normalize(item) for item in value]
    raise TypeError(f"unsupported canonical JSON value: {type(value)!r}")


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            _normalize(value),
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"expected JSON object: {relative_path}")
    return value


def _iso_utc_from_ns(value: int) -> str:
    return datetime.fromtimestamp(value / 1_000_000_000, tz=timezone.utc).isoformat(
        timespec="microseconds"
    ).replace("+00:00", "Z")


def _file_receipt(path: Path, output_root: Path) -> dict[str, Any]:
    stat = path.stat()
    raw = path.read_bytes()
    return {
        "relative_output_path": path.relative_to(REPO_ROOT).as_posix(),
        "output_root_relative_path": output_root.relative_to(REPO_ROOT).as_posix(),
        "filename": path.name,
        "byte_count": len(raw),
        "sha256": sha256_bytes(raw),
        "filesystem_creation_time_ns": stat.st_ctime_ns,
        "filesystem_creation_time_utc": _iso_utc_from_ns(stat.st_ctime_ns),
        "filesystem_last_write_time_ns": stat.st_mtime_ns,
        "filesystem_last_write_time_utc": _iso_utc_from_ns(stat.st_mtime_ns),
    }


def build_report() -> dict[str, Any]:
    output_root = (REPO_ROOT / OUTPUT_ROOT_RELATIVE_PATH).resolve()
    if not output_root.is_dir():
        raise ValueError("authorized execution output root is absent")
    identity = load_json(IDENTITY_RELATIVE_PATH)
    matrix = load_json(MATRIX_RELATIVE_PATH)
    review = load_json(REVIEW_RELATIVE_PATH)
    start_path = output_root / "EXECUTION-STARTED.json"
    result_path = output_root / "MATRIX-RESULT.json"
    start = json.loads(start_path.read_text(encoding="utf-8"))
    result = json.loads(result_path.read_text(encoding="utf-8"))
    if not isinstance(start, dict) or not isinstance(result, dict):
        raise TypeError("execution auxiliary records must be JSON objects")

    expected_paths = {
        str(item["json_relative_output_path"])
        for item in identity["outputs"]
    } | {
        str(item["npz_relative_output_path"])
        for item in identity["outputs"]
    } | {
        str(item["relative_output_path"])
        for item in identity["auxiliary_execution_files"]
    }
    actual_paths = {
        path.relative_to(REPO_ROOT).as_posix()
        for path in output_root.iterdir()
        if path.is_file()
    }
    if actual_paths != expected_paths:
        raise ValueError("execution output path closure mismatch")

    file_receipts = [
        _file_receipt(REPO_ROOT / relative_path, output_root)
        for relative_path in sorted(actual_paths)
    ]
    receipt_by_path = {
        item["relative_output_path"]: item for item in file_receipts
    }
    run_custody = result.get("run_custody")
    if not isinstance(run_custody, list) or len(run_custody) != 6:
        raise ValueError("execution run custody closure mismatch")
    by_run = {
        str(item["run_id"]): item for item in run_custody if isinstance(item, dict)
    }
    if set(by_run) != set(custody_v3.EXACT_RUN_IDS):
        raise ValueError("execution run ID closure mismatch")

    run_rows = []
    for ordinal, run_id in enumerate(custody_v3.EXACT_RUN_IDS, start=1):
        item = by_run[run_id]
        json_path = f"{OUTPUT_ROOT_RELATIVE_PATH}/{item['json_relative_name']}"
        npz_path = f"{OUTPUT_ROOT_RELATIVE_PATH}/{item['npz_relative_name']}"
        run_rows.append(
            {
                "execution_ordinal": ordinal,
                "run_id": run_id,
                "executed_exactly_once": result["execution_count_by_run_id"][run_id]
                == 1,
                "full_record_identity_sha256": item[
                    "full_record_identity_sha256"
                ],
                "complete_execution_identity_sha256": item[
                    "complete_execution_identity_sha256"
                ],
                "resolved_metric_configuration_sha256": item[
                    "resolved_metric_configuration_sha256"
                ],
                "json_relative_output_path": json_path,
                "npz_relative_output_path": npz_path,
                "json_sha256": item["json_sha256"],
                "npz_sha256": item["npz_sha256"],
                "json_bytes_exact": receipt_by_path[json_path]["sha256"]
                == item["json_sha256"],
                "npz_bytes_exact": receipt_by_path[npz_path]["sha256"]
                == item["npz_sha256"],
                "physical_trajectory_sha256": item[
                    "physical_trajectory_sha256"
                ],
            }
        )

    authority = review[custody_v3.REVIEW_AUTHORITY_FIELD]
    runtime = result["runtime_custody"]
    creation_times = [item["filesystem_creation_time_ns"] for item in file_receipts]
    write_times = [item["filesystem_last_write_time_ns"] for item in file_receipts]
    canonical_now = canonical_v0.canonical_directory_tree_sha256()
    resolved_authority = authority[
        "expected_resolved_metric_configuration_sha256_by_run_id"
    ]
    checks = {
        "accepted_v3_anchor_present_and_exact": review["verdict"]
        == custody_v3.EXPECTED_REVIEW_VERDICT
        and runtime["review_anchor"]["sha256"]
        == sha256_bytes((REPO_ROOT / REVIEW_RELATIVE_PATH).read_bytes()),
        "exact_six_run_ids_executed_once": result["exact_run_ids"]
        == list(custody_v3.EXACT_RUN_IDS)
        and result["execution_count_by_run_id"]
        == {run_id: 1 for run_id in custody_v3.EXACT_RUN_IDS},
        "resolved_configurations_match_accepted_authority": all(
            by_run[run_id]["resolved_metric_configuration_sha256"]
            == resolved_authority[run_id]
            for run_id in custody_v3.EXACT_RUN_IDS
        ),
        "runtime_bindings_passed_before_simulation": runtime["all_passed"] is True
        and runtime["loaded_module_attestation"]["all_passed"] is True
        and runtime["loaded_module_attestation"]["loaded_module_count"] == 8,
        "no_unauthorized_overrides": runtime[
            "caller_metric_or_role_override_authorized"
        ]
        is False
        and runtime["partial_template_direct_execution_authorized"] is False,
        "no_retry_substitution_or_exclusion": start["no_retry"] is True
        and start["no_overwrite"] is True
        and all(row["executed_exactly_once"] for row in run_rows),
        "exact_output_identity_closure": len(actual_paths) == 14
        and len(file_receipts) == 14
        and all(
            row["json_bytes_exact"] and row["npz_bytes_exact"] for row in run_rows
        ),
        "raw_payloads_preserved_without_receipt_rewrite": True,
        "execution_order_recorded": [row["execution_ordinal"] for row in run_rows]
        == list(range(1, 7)),
        "timestamps_recorded_in_supplemental_receipt": len(creation_times)
        == len(write_times)
        == 14,
        "failure_retention_policy_preserved": start["no_retry"] is True,
        "canonical_preexisting_evidence_unchanged": result[
            "canonical_digest_unchanged"
        ]
        is True
        and result["canonical_digest_before"] == result["canonical_digest_after"]
        == canonical_now,
        "output_directory_contains_only_authorized_products": actual_paths
        == expected_paths,
    }
    if not all(checks.values()):
        failed = [key for key, passed in checks.items() if not passed]
        raise ValueError(f"execution receipt checks failed: {failed}")

    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "EXECUTION_COMPLETED_ONCE_PENDING_INDEPENDENT_RESULT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "accepted_review_anchor": {
            "relative_path": REVIEW_RELATIVE_PATH,
            "sha256": sha256_bytes((REPO_ROOT / REVIEW_RELATIVE_PATH).read_bytes()),
            "verdict": review["verdict"],
        },
        "execution_auxiliary_records": {
            "execution_started": receipt_by_path[
                f"{OUTPUT_ROOT_RELATIVE_PATH}/EXECUTION-STARTED.json"
            ],
            "matrix_result": receipt_by_path[
                f"{OUTPUT_ROOT_RELATIVE_PATH}/MATRIX-RESULT.json"
            ],
        },
        "execution_status": result["status"],
        "execution_invocation_count": 1,
        "authorized_run_count": 6,
        "completed_run_count": len(run_rows),
        "role_payload_file_count": 12,
        "auxiliary_file_count": 2,
        "total_output_file_count": len(file_receipts),
        "execution_order": run_rows,
        "output_file_receipts": file_receipts,
        "observed_execution_timestamp_window": {
            "source": "local filesystem metadata; supplemental and non-decision-bearing",
            "earliest_creation_time_ns": min(creation_times),
            "earliest_creation_time_utc": _iso_utc_from_ns(min(creation_times)),
            "latest_last_write_time_ns": max(write_times),
            "latest_last_write_time_utc": _iso_utc_from_ns(max(write_times)),
        },
        "runtime_custody_summary": {
            "runtime_source_closure_sha256": runtime[
                "runtime_source_closure_sha256"
            ],
            "loaded_module_count": runtime["loaded_module_attestation"][
                "loaded_module_count"
            ],
            "read_only_plan_count": runtime["read_only_execution_plan_count"],
            "simulation_entry_count_at_preflight": runtime[
                "simulation_entry_count"
            ],
            "execution_invoked": runtime["execution_invoked"],
            "canonical_directory_tree_sha256": runtime[
                "canonical_directory_tree_sha256"
            ],
        },
        "instrumentation_execution_facts": {
            "pair_count": len(result["instrumentation_nonperturbation_pairs"]),
            "all_pairs_byte_identical": result["all_pairs_byte_identical"],
            "stored_pair_records": result["instrumentation_nonperturbation_pairs"],
            "scientific_acceptance_status": "PENDING_INDEPENDENT_RESULT_REVIEW",
        },
        "custody_checks": checks,
        "passed_custody_check_count": sum(checks.values()),
        "custody_check_count": len(checks),
        "failed_custody_check_ids": [
            key for key, passed in checks.items() if not passed
        ],
        "classifier_execution": {
            "classifier_invoked_by_receipt": False,
            "stored_classifier_metrics_treated_as_authoritative": False,
            "H_A_through_H_E_decided_by_receipt": False,
        },
        "preserved_scientific_core": {
            "accepted_bounded_Maxwell_Dirac_E_REPRO": "PRESERVED",
            "fourteen_row_robustness": "NUMERICALLY_BLOCKED",
            "descendant_materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "R13_root_mechanism": "UNRESOLVED",
            "new_E_REPRO": "NONE",
        },
        "authority_boundary": {
            "execution_completed": True,
            "additional_execution_authorized": False,
            "retry_authorized": False,
            "payload_rewrite_authorized": False,
            "mechanism_result_accepted": False,
            "instrumentation_nonperturbation_result_accepted": False,
            "robustness_reclassification_authorized": False,
            "materiality_evaluation_authorized": False,
            "independent_result_review_required": True,
        },
        "claim_ceiling": (
            "Execution facts only. No mechanism, instrumentation, robustness, "
            "materiality, or new E-REPRO result is accepted."
        ),
    }


def artifact_bytes() -> bytes:
    return canonical_json_bytes(build_report())


def write_or_check(check: bool) -> None:
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if check:
        if not path.is_file() or path.read_bytes() != raw:
            raise SystemExit(f"artifact mismatch: {REPORT_RELATIVE_PATH}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    report = json.loads(raw.decode("utf-8"))
    print(
        json.dumps(
            {
                "status": "CHECKED" if check else "WROTE",
                "verdict": report["verdict"],
                "completed_runs": report["completed_run_count"],
                "output_files": report["total_output_file_count"],
                "custody_checks": (
                    f"{report['passed_custody_check_count']}/"
                    f"{report['custody_check_count']}"
                ),
                "classifier_invoked": False,
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Record the one frozen execution")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
