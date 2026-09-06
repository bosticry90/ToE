from __future__ import annotations

"""Independently review the preserved R13 mechanism experiment evidence.

This review is read-only with respect to the accepted freeze, the fourteen
execution outputs, and the canonical evidence tree.  It first reconstructs
custody and stored-trajectory identity, then invokes the exact frozen v3 raw
assembler and its sole public classifier entry point.  A frozen observable-
semantics failure blocks H_A--H_E rather than being repaired or bypassed.
"""

import argparse
import hashlib
import json
import math
import struct
import unicodedata
from collections.abc import Mapping
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v3
    as classifier_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_execution_v0
    as execution_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v3
    as custody_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0
    as canonical_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as raw_v3,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-16T00:00:00Z"
TARGET = execution_v0.SELECTED_NEXT_TARGET
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_observable_semantics_"
    "reconciliation_packet_v1"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RESULT_REVIEW_20260716_v0"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RESULT_REVIEW_"
    "20260716_v0.json"
)
EXPECTED_OUTPUT_TREE_SHA256 = (
    "95c8209137bfb60796f53d943c99dbef6f6b80e29fad0899d36a775404d34f51"
)
EXPECTED_EXECUTION_RECEIPT_SHA256 = (
    "387d636a4a49c1a9cc61abf584bd9c58fd948c054da22657cb8a75e27209afc2"
)
EXPECTED_REVIEW_ANCHOR_SHA256 = (
    "d619fd8048a4c7fd6ad49438a7363578ee24e215de7b83f190b1127399464f1a"
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


def _load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"expected JSON object: {path}")
    return value


def _ulp_distance(left: float, right: float) -> int:
    """Return binary64 representable-step distance for nonnegative values."""

    if left < 0.0 or right < 0.0:
        raise ValueError("ULP audit is defined here only for nonnegative shares")
    left_bits = struct.unpack(">Q", struct.pack(">d", float(left)))[0]
    right_bits = struct.unpack(">Q", struct.pack(">d", float(right)))[0]
    return abs(left_bits - right_bits)


def _mapping_mismatches(
    stored: Mapping[str, Any], expected: Mapping[str, float]
) -> list[dict[str, Any]]:
    mismatches: list[dict[str, Any]] = []
    for block_id in raw_v3.BLOCK_IDS:
        actual = float(stored[block_id])
        wanted = float(expected[block_id])
        if actual != wanted:
            mismatches.append(
                {
                    "block_id": block_id,
                    "stored": actual,
                    "recomputed": wanted,
                    "ulp_distance": _ulp_distance(actual, wanted),
                }
            )
    return mismatches


def _audit_summary_arithmetic(
    payloads: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    per_role: list[dict[str, Any]] = []
    first_python_mismatch: dict[str, Any] | None = None
    total_records = 0
    total_scalar_fields = 0
    raw_mismatches = 0
    normalized_mismatches = 0
    numpy_share_mismatches = 0
    python_share_mismatches = 0
    maximum_ulp_distance = 0

    for run_id in (
        "MECHv0:R13_LOOSE:INSTRUMENTED",
        "MECHv0:R13_TIGHT:INSTRUMENTED",
        "MECHv0:R10_LOOSE:INSTRUMENTED",
    ):
        payload = payloads[run_id]
        tolerance = float(payload["configuration"]["solver_tolerance"])
        role_counts = {
            "summary_record_count": 0,
            "raw_scalar_mismatch_count": 0,
            "normalized_scalar_mismatch_count": 0,
            "numpy_share_scalar_mismatch_count": 0,
            "python_share_scalar_mismatch_count": 0,
        }

        records: list[tuple[str, int, int | None, Mapping[str, Any], np.ndarray]] = []
        for step in payload["raw_events"]["solver_steps"]:
            for event in step["iteration_events"]:
                records.append(
                    (
                        "iteration",
                        int(step["step"]),
                        int(event["iteration"]),
                        event,
                        np.asarray(event["packed_update_defect"]),
                    )
                )
        for event in payload["raw_events"]["terminal_equation_blocks"]:
            records.append(
                (
                    "terminal",
                    int(event["step"]),
                    None,
                    event,
                    np.asarray(event["packed_terminal_equation_defect"]),
                )
            )

        for family, step, iteration, event, defect in records:
            raw = raw_v3._block_maxima(defect)
            denominator = max(tolerance, raw_v3.GAMMA64)
            normalized = {
                block_id: raw[block_id] / denominator
                for block_id in raw_v3.BLOCK_IDS
            }
            python_total = sum(normalized.values()) + raw_v3.GAMMA64
            python_shares = {
                block_id: normalized[block_id] / python_total
                for block_id in raw_v3.BLOCK_IDS
            }
            stacked = np.stack(
                [
                    np.asarray([normalized[block_id]], dtype=np.float64)
                    for block_id in raw_v3.BLOCK_IDS
                ],
                axis=0,
            )
            numpy_total = float(
                np.sum(stacked, axis=0)[0] + raw_v3.GAMMA64
            )
            numpy_shares = {
                block_id: normalized[block_id] / numpy_total
                for block_id in raw_v3.BLOCK_IDS
            }

            raw_bad = _mapping_mismatches(event["packed_real_block_maxima"], raw)
            normalized_bad = _mapping_mismatches(
                event["normalized_block_magnitudes"], normalized
            )
            numpy_bad = _mapping_mismatches(
                event["dominance_share_by_block"], numpy_shares
            )
            python_bad = _mapping_mismatches(
                event["dominance_share_by_block"], python_shares
            )
            role_counts["summary_record_count"] += 1
            role_counts["raw_scalar_mismatch_count"] += len(raw_bad)
            role_counts["normalized_scalar_mismatch_count"] += len(normalized_bad)
            role_counts["numpy_share_scalar_mismatch_count"] += len(numpy_bad)
            role_counts["python_share_scalar_mismatch_count"] += len(python_bad)
            if python_bad:
                maximum_ulp_distance = max(
                    maximum_ulp_distance,
                    *(item["ulp_distance"] for item in python_bad),
                )
                if first_python_mismatch is None:
                    first_item = python_bad[0]
                    first_python_mismatch = {
                        "run_id": run_id,
                        "event_family": family,
                        "step": step,
                        "iteration": iteration,
                        "block_id": first_item["block_id"],
                        "stored_numpy_producer_value": first_item["stored"],
                        "frozen_python_sum_verifier_value": first_item[
                            "recomputed"
                        ],
                        "ulp_distance": first_item["ulp_distance"],
                        "numpy_reduction_total": numpy_total,
                        "python_scalar_sum_total": python_total,
                    }

        role_scalar_count = role_counts["summary_record_count"] * len(
            raw_v3.BLOCK_IDS
        )
        role_counts["scalar_field_count_per_mapping"] = role_scalar_count
        per_role.append({"run_id": run_id, **role_counts})
        total_records += role_counts["summary_record_count"]
        total_scalar_fields += role_scalar_count
        raw_mismatches += role_counts["raw_scalar_mismatch_count"]
        normalized_mismatches += role_counts[
            "normalized_scalar_mismatch_count"
        ]
        numpy_share_mismatches += role_counts[
            "numpy_share_scalar_mismatch_count"
        ]
        python_share_mismatches += role_counts[
            "python_share_scalar_mismatch_count"
        ]

    if first_python_mismatch is None:
        raise ValueError("expected frozen verifier arithmetic mismatch was absent")
    return {
        "audited_instrumented_run_count": len(per_role),
        "block_count": len(raw_v3.BLOCK_IDS),
        "summary_record_count": total_records,
        "scalar_field_count_per_mapping": total_scalar_fields,
        "stored_raw_maximum_mismatch_count": raw_mismatches,
        "stored_normalized_mismatch_count": normalized_mismatches,
        "stored_share_vs_numpy_producer_mismatch_count": numpy_share_mismatches,
        "stored_share_vs_frozen_python_sum_verifier_mismatch_count": (
            python_share_mismatches
        ),
        "maximum_python_sum_mismatch_ulp_distance": maximum_ulp_distance,
        "first_frozen_verifier_mismatch": first_python_mismatch,
        "per_role": per_role,
        "forensic_classification": (
            "REDUCTION_ORDER_MISMATCH_BETWEEN_NUMPY_PRODUCER_AND_"
            "PYTHON_SCALAR_SUM_VERIFIER"
        ),
        "evidence_bytes_modified": False,
        "frozen_verifier_bypassed_for_mechanism_classification": False,
    }


def _load_and_validate_payloads(
    matrix: Mapping[str, Any], execution_report: Mapping[str, Any]
) -> tuple[dict[str, Mapping[str, Any]], dict[str, np.ndarray]]:
    receipt_by_run = {
        item["run_id"]: item for item in execution_report["execution_order"]
    }
    payloads: dict[str, Mapping[str, Any]] = {}
    trajectories: dict[str, np.ndarray] = {}
    for record in matrix["records"]:
        run_id = str(record["run_id"])
        receipt = receipt_by_run[run_id]
        payload, _, _ = raw_v3._load_role_payload(
            REPO_ROOT / str(record["json_relative_output_path"]),
            REPO_ROOT / str(record["npz_relative_output_path"]),
            expected_run_id=run_id,
            expected_json_sha256=str(receipt["json_sha256"]),
            expected_npz_sha256=str(receipt["npz_sha256"]),
        )
        _, trajectory = raw_v3._validate_payload_identity(payload, record)
        payloads[run_id] = payload
        trajectories[run_id] = trajectory
    return payloads, trajectories


def _pair_audit(
    trajectories: Mapping[str, np.ndarray],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in ("R13_LOOSE", "R13_TIGHT", "R10_LOOSE"):
        instrumented_id = f"MECHv0:{case}:INSTRUMENTED"
        control_id = f"MECHv0:{case}:NONINSTRUMENTED_CONTROL"
        instrumented = trajectories[instrumented_id]
        control = trajectories[control_id]
        rows.append(
            {
                "physical_case": case,
                "instrumented_run_id": instrumented_id,
                "control_run_id": control_id,
                "shape": list(instrumented.shape),
                "all_17_checkpoint_arrays_exact": bool(
                    np.array_equal(instrumented, control)
                ),
                "raw_c_order_bytes_exact": (
                    instrumented.tobytes(order="C")
                    == control.tobytes(order="C")
                ),
                "instrumented_trajectory_sha256": (
                    raw_v3._physical_trajectory_sha256(instrumented)
                ),
                "control_trajectory_sha256": (
                    raw_v3._physical_trajectory_sha256(control)
                ),
            }
        )
    return rows


def build_report() -> dict[str, Any]:
    execution_report_path = REPO_ROOT / execution_v0.REPORT_RELATIVE_PATH
    execution_receipt_raw = execution_report_path.read_bytes()
    execution_report = _load_json(execution_report_path)
    matrix = execution_v0.load_json(execution_v0.MATRIX_RELATIVE_PATH)
    review_path = REPO_ROOT / execution_v0.REVIEW_RELATIVE_PATH
    accepted_review = _load_json(review_path)
    authority = accepted_review[custody_v3.REVIEW_AUTHORITY_FIELD]
    output_root = REPO_ROOT / execution_v0.OUTPUT_ROOT_RELATIVE_PATH
    matrix_result = _load_json(output_root / "MATRIX-RESULT.json")
    execution_started = _load_json(output_root / "EXECUTION-STARTED.json")

    output_tree_before = implementation_v0.directory_tree_sha256(output_root)
    canonical_tree_before = canonical_v0.canonical_directory_tree_sha256()
    regenerated_execution_receipt = execution_v0.artifact_bytes()

    expected_paths = {
        item["relative_output_path"]
        for item in execution_report["output_file_receipts"]
    }
    actual_paths = {
        path.relative_to(REPO_ROOT).as_posix()
        for path in output_root.iterdir()
        if path.is_file()
    }
    receipt_by_path = {
        item["relative_output_path"]: item
        for item in execution_report["output_file_receipts"]
    }
    output_hashes_exact = all(
        sha256_bytes((REPO_ROOT / relative_path).read_bytes())
        == receipt_by_path[relative_path]["sha256"]
        for relative_path in expected_paths
    )
    runtime_modules = authority["runtime_source_closure"]["modules"]
    runtime_source_bytes_exact = all(
        sha256_bytes((REPO_ROOT / item["relative_path"]).read_bytes())
        == item["sha256"]
        for item in runtime_modules
    )

    payloads, trajectories = _load_and_validate_payloads(
        matrix, execution_report
    )
    pair_rows = _pair_audit(trajectories)
    controls_have_no_mechanism_data = all(
        payloads[run_id]["raw_events"] is None
        and payloads[run_id]["metrics"] is None
        for run_id in payloads
        if run_id.endswith("NONINSTRUMENTED_CONTROL")
    )
    arithmetic_audit = _audit_summary_arithmetic(payloads)

    assembler_outcome: dict[str, Any]
    try:
        raw_v3.assemble_raw_evidence(REPO_ROOT)
    except raw_v3.RawEvidenceError as error:
        assembler_outcome = {
            "status": "BLOCKED",
            "evidence_result": error.evidence_result,
            "evidence_diagnostic": error.diagnostic,
            "evidence_detail": error.detail,
        }
    else:
        raise ValueError("frozen assembler unexpectedly admitted the evidence")

    classifier_result = classifier_v3.classify_from_raw_payloads(REPO_ROOT)
    classifier_repeat = classifier_v3.classify_from_raw_payloads(REPO_ROOT)
    classifier_deterministic = canonical_json_bytes(
        classifier_result
    ) == canonical_json_bytes(classifier_repeat)
    expected_hypotheses = {
        "H_A_CANCELLATION_CONDITIONING",
        "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
        "H_C_DISCRETE_CLOSURE_MISMATCH",
        "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
        "H_E_UNRESOLVED_MECHANISM",
    }
    all_hypotheses_not_evaluated = (
        set(classifier_result["hypothesis_decisions"]) == expected_hypotheses
        and all(
            item["status"] == "NOT_EVALUATED"
            for item in classifier_result["hypothesis_decisions"].values()
        )
    )

    output_tree_after = implementation_v0.directory_tree_sha256(output_root)
    canonical_tree_after = canonical_v0.canonical_directory_tree_sha256()
    custody_checks = {
        "accepted_v3_anchor_present_and_exact": (
            sha256_bytes(review_path.read_bytes()) == EXPECTED_REVIEW_ANCHOR_SHA256
            and accepted_review["verdict"]
            == custody_v3.EXPECTED_REVIEW_VERDICT
        ),
        "single_authorized_batch_was_consumed_once": (
            authority["one_execution_only"] is True
            and execution_report["execution_invocation_count"] == 1
            and matrix_result["status"] == "EXECUTION_COMPLETED_ONCE"
        ),
        "exact_six_registered_runs_executed_once": (
            matrix_result["exact_run_ids"] == list(custody_v3.EXACT_RUN_IDS)
            and matrix_result["execution_count_by_run_id"]
            == {run_id: 1 for run_id in custody_v3.EXACT_RUN_IDS}
        ),
        "exact_twelve_role_payloads_and_two_auxiliary_records_exist": (
            len(actual_paths) == 14
            and actual_paths == expected_paths
            and execution_report["role_payload_file_count"] == 12
            and execution_report["auxiliary_file_count"] == 2
        ),
        "every_output_name_hash_schema_and_role_reconstructs": (
            output_hashes_exact and len(payloads) == 6
        ),
        "full_output_tree_identity_reconstructs": (
            output_tree_before == EXPECTED_OUTPUT_TREE_SHA256
        ),
        "all_resolved_configurations_match_accepted_identities": all(
            item["resolved_metric_configuration_sha256"]
            == authority[
                "expected_resolved_metric_configuration_sha256_by_run_id"
            ][item["run_id"]]
            for item in execution_report["execution_order"]
        ),
        "all_eight_runtime_source_bindings_match": (
            len(runtime_modules) == 8 and runtime_source_bytes_exact
        ),
        "no_retry_substitution_exclusion_or_override_recorded": (
            execution_started["no_retry"] is True
            and execution_started["no_overwrite"] is True
            and execution_report["custody_checks"][
                "no_retry_substitution_or_exclusion"
            ]
            is True
            and execution_report["custody_checks"]["no_unauthorized_overrides"]
            is True
        ),
        "canonical_evidence_tree_remains_unchanged": (
            canonical_tree_before
            == canonical_tree_after
            == raw_v3.EXPECTED_CANONICAL_TREE_SHA256
        ),
        "raw_payloads_remain_byte_preserved": (
            output_tree_before == output_tree_after
        ),
        "supplemental_timestamp_receipt_is_non_decision_bearing": (
            execution_report["observed_execution_timestamp_window"]["source"]
            == "local filesystem metadata; supplemental and non-decision-bearing"
        ),
        "execution_receipt_reconstructs_exactly": (
            sha256_bytes(execution_receipt_raw)
            == EXPECTED_EXECUTION_RECEIPT_SHA256
            and execution_receipt_raw == regenerated_execution_receipt
        ),
    }
    if not all(custody_checks.values()):
        failed = [key for key, passed in custody_checks.items() if not passed]
        raise ValueError(f"independent custody checks failed: {failed}")
    if not all(
        row["all_17_checkpoint_arrays_exact"]
        and row["raw_c_order_bytes_exact"]
        and row["instrumented_trajectory_sha256"]
        == row["control_trajectory_sha256"]
        for row in pair_rows
    ):
        raise ValueError("stored-trajectory nonperturbation gate failed")
    expected_arithmetic = {
        "summary_record_count": 224,
        "scalar_field_count_per_mapping": 1792,
        "stored_raw_maximum_mismatch_count": 0,
        "stored_normalized_mismatch_count": 0,
        "stored_share_vs_numpy_producer_mismatch_count": 0,
        "stored_share_vs_frozen_python_sum_verifier_mismatch_count": 570,
        "maximum_python_sum_mismatch_ulp_distance": 2,
    }
    if any(
        arithmetic_audit[key] != value
        for key, value in expected_arithmetic.items()
    ):
        raise ValueError("observable-semantics mismatch census changed")
    if (
        assembler_outcome["evidence_result"] != "BLOCKED_OBSERVABLE_SEMANTICS"
        or assembler_outcome["evidence_diagnostic"]
        != "RAW_SUMMARY_RECOMPUTATION_MISMATCH"
        or classifier_result["evidence_result"]
        != "BLOCKED_OBSERVABLE_SEMANTICS"
        or classifier_result["evidence_diagnostic"]
        != "RAW_SUMMARY_RECOMPUTATION_MISMATCH"
        or classifier_result["aggregate_mechanism_result"] != "BLOCKED"
        or classifier_result["supported_mechanism_ids"] != []
        or not all_hypotheses_not_evaluated
        or not classifier_deterministic
    ):
        raise ValueError("frozen classifier did not fail closed as required")

    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "BLOCKED_OBSERVABLE_SEMANTICS",
        "first_diagnostic": "RAW_SUMMARY_RECOMPUTATION_MISMATCH",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "consumed_execution_receipt": {
            "relative_path": execution_v0.REPORT_RELATIVE_PATH,
            "sha256": sha256_bytes(execution_receipt_raw),
            "verdict": execution_report["verdict"],
        },
        "custody_review": {
            "status": "ACCEPTED",
            "output_tree_sha256": output_tree_before,
            "canonical_tree_sha256": canonical_tree_before,
            "run_count": 6,
            "role_payload_file_count": 12,
            "auxiliary_record_count": 2,
            "runtime_source_binding_count": len(runtime_modules),
            "checks": custody_checks,
            "passed_check_count": sum(custody_checks.values()),
            "check_count": len(custody_checks),
            "failed_check_ids": [
                key for key, passed in custody_checks.items() if not passed
            ],
        },
        "instrumentation_nonperturbation_review": {
            "status": "FROZEN_STORED_TRAJECTORY_GATE_PASSED",
            "pair_count": len(pair_rows),
            "checkpoint_count_including_initial": 17,
            "packed_state_width": 352,
            "pairs": pair_rows,
            "accepted_scope": (
                "Every saved physical state at every accepted checkpoint is "
                "byte-identical within all three instrumented/control pairs."
            ),
            "withheld_scope": (
                "No claim is made about unsaved internal solver iterations in "
                "the controls."
            ),
            "controls_have_no_mechanism_payload": controls_have_no_mechanism_data,
        },
        "raw_reconstruction_review": {
            "status": "BLOCKED",
            "frozen_assembler_outcome": assembler_outcome,
            "arithmetic_forensics": arithmetic_audit,
            "interpretation": (
                "The stored summaries exactly match the NumPy reduction used "
                "by the producer.  The frozen verifier uses Python scalar sum "
                "for the same eight normalized values, producing 1--2 ULP "
                "differences.  Exact-equality policy therefore blocks the "
                "evidence even though the preserved bytes are internally "
                "consistent with their producer."
            ),
        },
        "classifier_review": {
            "public_entry_point": "classify_from_raw_payloads",
            "invocation_count": 2,
            "deterministic": classifier_deterministic,
            "evidence_result": classifier_result["evidence_result"],
            "evidence_diagnostic": classifier_result["evidence_diagnostic"],
            "evidence_detail": classifier_result["evidence_detail"],
            "aggregate_mechanism_result": classifier_result[
                "aggregate_mechanism_result"
            ],
            "supported_mechanism_ids": classifier_result[
                "supported_mechanism_ids"
            ],
            "hypothesis_status_by_id": {
                key: value["status"]
                for key, value in classifier_result[
                    "hypothesis_decisions"
                ].items()
            },
            "H_A_through_H_E_all_not_evaluated": all_hypotheses_not_evaluated,
            "H_E_not_assigned": classifier_result["hypothesis_decisions"][
                "H_E_UNRESOLVED_MECHANISM"
            ]["status"]
            == "NOT_EVALUATED",
        },
        "preserved_scientific_core": {
            "accepted_bounded_Maxwell_Dirac_E_REPRO": "PRESERVED",
            "fourteen_row_robustness": "NUMERICALLY_BLOCKED",
            "descendant_materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "R13_root_mechanism": "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "authority_boundary": {
            "additional_execution_authorized": False,
            "retry_authorized": False,
            "payload_rewrite_authorized": False,
            "frozen_assembler_or_classifier_rewrite_authorized": False,
            "H_A_through_H_E_acceptance_authorized": False,
            "robustness_reclassification_authorized": False,
            "materiality_evaluation_authorized": False,
            "new_E_REPRO_authorized": False,
            "bounded_versioned_observable_semantics_reconciliation_authorized": (
                True
            ),
        },
        "required_reconciliation_scope": {
            "must_preserve_all_fourteen_output_files": True,
            "must_not_rerun_simulation": True,
            "must_not_modify_v3_freeze_or_review_anchor": True,
            "must_version_any_successor_assembler_and_classifier": True,
            "must_freeze_one_canonical_float64_reduction_algorithm": True,
            "must_test_numpy_and_python_reduction_order_divergence": True,
            "must_independently_review_successor_before_classification": True,
            "may_adjudicate_only_the_existing_preserved_evidence": True,
        },
        "claim_ceiling": (
            "Custody and saved-trajectory byte identity are accepted. Raw "
            "mechanism evidence is blocked by frozen observable semantics; no "
            "H_A--H_E result, robustness reclassification, materiality result, "
            "physical-instability claim, or new E-REPRO is authorized."
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
                "custody_checks": (
                    f"{report['custody_review']['passed_check_count']}/"
                    f"{report['custody_review']['check_count']}"
                ),
                "trajectory_pairs": report[
                    "instrumentation_nonperturbation_review"
                ]["pair_count"],
                "frozen_summary_mismatches": report[
                    "raw_reconstruction_review"
                ]["arithmetic_forensics"][
                    "stored_share_vs_frozen_python_sum_verifier_mismatch_count"
                ],
                "mechanism_result": report["classifier_review"][
                    "aggregate_mechanism_result"
                ],
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Review the preserved R13 mechanism evidence"
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
