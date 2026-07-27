from __future__ import annotations

"""Review the single v2 reconciliation invocation after its pre-terminal stop.

The authorized invocation failed closed before a comparison artifact was
created.  This review identifies the exact custody-contract mismatch without
re-entering the comparison, reading payload arrays, changing accepted evidence,
or authorizing a retry.
"""

import argparse
import hashlib
import inspect
import json
import math
import unicodedata
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_packet_review_v2
    as packet_review_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v2
    as reconciliation_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as raw_v3,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-17T00:00:00Z"
TARGET = reconciliation_v2.EXPECTED_REVIEW_NEXT_TARGET
SELECTED_NEXT_TARGET = (
    "terminate_dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_observable_semantics_"
    "reconciliation_lane_preserve_unresolved_r13"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_RESULT_REVIEW_20260717_v2"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_RESULT_REVIEW_20260717_v2.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_result_review_v2.py"
)
SOURCE_OUTPUT_ROOT_RELATIVE_PATH = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
)
EXECUTION_STARTED_RELATIVE_PATH = (
    f"{SOURCE_OUTPUT_ROOT_RELATIVE_PATH}/EXECUTION-STARTED.json"
)
EXPECTED_PACKET_REVIEW_SHA256 = (
    "e8c2d8d620210955298f1d5c654eecb92a27856ed7a8f1b8d61d8cb41e294171"
)
EXPECTED_RAW_ASSEMBLER_SHA256 = (
    "8ffaafcbb2de122611c0355b0e187b2ced9b16fb7d9ac2f78915883bb4c2215f"
)
EXPECTED_EXECUTION_STARTED_SHA256 = (
    "c1b58271592993bdcc5d86380bc9d6fb1d337efe4bbdbe7898c7027ff0ca4049"
)


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


def _load_json(relative_path: str) -> tuple[dict[str, Any], bytes]:
    path = REPO_ROOT / relative_path
    raw = path.read_bytes()
    value = json.loads(raw.decode("utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value, raw


def _source_binding(relative_path: str) -> dict[str, str]:
    path = REPO_ROOT / relative_path
    if not path.is_file():
        raise ValueError(f"missing result-review source: {relative_path}")
    return {"relative_path": relative_path, "sha256": sha256_bytes(path.read_bytes())}


def build_review() -> dict[str, Any]:
    packet_review, packet_review_raw = _load_json(packet_review_v2.REPORT_RELATIVE_PATH)
    marker, marker_raw = _load_json(EXECUTION_STARTED_RELATIVE_PATH)
    source_root = REPO_ROOT / SOURCE_OUTPUT_ROOT_RELATIVE_PATH
    result_root = REPO_ROOT / reconciliation_v2.RESULT_OUTPUT_ROOT_RELATIVE_PATH
    raw_assembler_path = REPO_ROOT / raw_v3.__file__.split("ToE\\", 1)[-1]
    raw_assembler_relative_path = raw_assembler_path.resolve().relative_to(REPO_ROOT).as_posix()
    raw_assembler_raw = raw_assembler_path.read_bytes()
    guard_source = inspect.getsource(raw_v3._validate_auxiliary_result)

    runtime_custody = marker.get("runtime_custody")
    if not isinstance(runtime_custody, Mapping):
        raise ValueError("execution marker runtime_custody is not a mapping")
    exact_run_ids = runtime_custody.get("exact_run_ids")
    requested_run_ids = runtime_custody.get("requested_run_ids")
    expected_run_ids = list(raw_v3.EXPECTED_RUN_IDS)
    source_tree_before = implementation_v0.directory_tree_sha256(source_root)

    checks = {
        "accepted_packet_review_exact": (
            sha256_bytes(packet_review_raw) == EXPECTED_PACKET_REVIEW_SHA256
            and packet_review.get("verdict") == reconciliation_v2.EXPECTED_REVIEW_VERDICT
            and packet_review.get("selected_next_target") == TARGET
        ),
        "source_tree_preserved_exact": (
            source_tree_before == reconciliation_v2.EXPECTED_SOURCE_OUTPUT_TREE_SHA256
        ),
        "execution_marker_exact": (
            sha256_bytes(marker_raw) == EXPECTED_EXECUTION_STARTED_SHA256
        ),
        "raw_assembler_source_exact": (
            sha256_bytes(raw_assembler_raw) == EXPECTED_RAW_ASSEMBLER_SHA256
        ),
        "producer_marker_uses_exact_run_ids": exact_run_ids == expected_run_ids,
        "producer_marker_omits_requested_run_ids": requested_run_ids is None,
        "assembler_guard_requires_requested_run_ids": (
            'start["runtime_custody"].get("requested_run_ids")' in guard_source
            and "!= list(EXPECTED_RUN_IDS)" in guard_source
            and '"EXECUTION_START_MARKER_INVALID"' in guard_source
        ),
        "result_root_absent_after_single_invocation": not result_root.exists(),
        "no_reconciliation_terminal_artifact_exists": not (
            REPO_ROOT / reconciliation_v2.RESULT_RELATIVE_PATH
        ).exists(),
    }
    source_tree_after = implementation_v0.directory_tree_sha256(source_root)
    checks["review_is_read_only_over_preserved_evidence"] = (
        source_tree_before == source_tree_after and not result_root.exists()
    )
    if not all(checks.values()):
        failed = [key for key, value in checks.items() if not value]
        raise ValueError(f"pre-terminal result review failed: {failed}")

    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "BLOCKED_RECONCILIATION_PRETERMINAL_INPUT_CONTRACT_MISMATCH",
        "first_diagnostic": "EXECUTION_START_RUN_ID_KEY_MISMATCH",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "reviewed_authority": {
            "relative_path": packet_review_v2.REPORT_RELATIVE_PATH,
            "sha256": sha256_bytes(packet_review_raw),
            "verdict": packet_review["verdict"],
        },
        "review_sources": {
            "raw_evidence_assembler": {
                "relative_path": raw_assembler_relative_path,
                "sha256": sha256_bytes(raw_assembler_raw),
            },
            "execution_started_marker": {
                "relative_path": EXECUTION_STARTED_RELATIVE_PATH,
                "sha256": sha256_bytes(marker_raw),
            },
            "focused_test": _source_binding(TEST_RELATIVE_PATH),
        },
        "calculation_invocation_review": {
            "authorized_invocation_count": 1,
            "observed_invocation_count_this_cycle": 1,
            "completed_comparison_count": 0,
            "derived_result_artifact_count": 0,
            "terminal_classification": "NOT_ASSIGNED_PRETERMINAL",
            "field_count_compared": 0,
            "payload_comparison_completed": False,
            "simulation_invoked": False,
            "historical_outputs_modified": False,
            "source_output_tree_sha256_before": source_tree_before,
            "source_output_tree_sha256_after": source_tree_after,
        },
        "input_contract_mismatch": {
            "producer_marker_schema_id": marker.get("schema_id"),
            "producer_runtime_key": "exact_run_ids",
            "producer_runtime_value": exact_run_ids,
            "consumer_required_runtime_key": "requested_run_ids",
            "consumer_observed_runtime_value": requested_run_ids,
            "consumer_expected_runtime_value": expected_run_ids,
            "raised_result": "BLOCKED_CUSTODY",
            "raised_diagnostic": "EXECUTION_START_MARKER_INVALID",
            "classification": "PRODUCTION_CONSUMER_CONTRACT_MISMATCH",
            "evidence_arrays_needed_to_diagnose": False,
        },
        "independent_review_checks": {
            "checks": checks,
            "passed_check_count": sum(checks.values()),
            "check_count": len(checks),
            "actual_payload_arrays_read_during_result_review": False,
            "calculation_reentered_during_result_review": False,
        },
        "hard_stop": {
            "retry_authorized": False,
            "second_calculation_authorized": False,
            "packet_v3_authorized": False,
            "simulation_authorized": False,
            "source_output_rewrite_authorized": False,
            "raw_assembler_repair_authorized_in_closed_lane": False,
            "reconciliation_lane_terminated": True,
        },
        "preserved_scientific_core": {
            "accepted_bounded_Maxwell_Dirac_E_REPRO": "PRESERVED",
            "fourteen_row_robustness": "NUMERICALLY_BLOCKED",
            "descendant_materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "H_A_through_H_E": "NOT_EVALUATED",
            "R13_root_mechanism": "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "claim_ceiling": (
            "Independent review of a fail-closed pre-terminal calculation stop only. "
            "No reconciliation terminal label was assigned because complete input "
            "validation did not finish. No H_A-H_E result, canonical semantics, "
            "robustness reclassification, materiality result, simulation, seam closure, "
            "master-action promotion, or new E-REPRO follows."
        ),
    }


def artifact_bytes() -> bytes:
    return canonical_json_bytes(build_review())


def write_or_check(check: bool) -> None:
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if check:
        if not path.is_file() or path.read_bytes() != raw:
            raise SystemExit(f"artifact mismatch: {REPORT_RELATIVE_PATH}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    review = json.loads(raw.decode("utf-8"))
    print(
        json.dumps(
            {
                "status": "CHECKED" if check else "WROTE",
                "verdict": review["verdict"],
                "first_diagnostic": review["first_diagnostic"],
                "terminal_classification": review["calculation_invocation_review"][
                    "terminal_classification"
                ],
                "reconciliation_lane_terminated": review["hard_stop"][
                    "reconciliation_lane_terminated"
                ],
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Review the fail-closed v2 reconciliation invocation"
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
