from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PREFIX = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v1"
)
RESULT_RELATIVE_PATH = f"{PREFIX}.json"
SIDECAR_RELATIVE_PATH = f"{PREFIX}.json.sha256"
MARKER_RELATIVE_PATH = f"{PREFIX}.authority_consumed.json"
STAGES_RELATIVE_PATH = f"{PREFIX}.stages.json"
LOG_RELATIVE_PATH = f"{PREFIX}.log"
SOURCE_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v1.py"
)
V0_SOURCE_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v0.py"
)
HUMAN_RESULT_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_EXECUTION_RESULT_20260719_v1.md"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_EXECUTION_RESULT_REVIEW_20260719_v1.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_execution_result_review_v1.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereKernelExploratorySandboxExecutionResultReviewV1.lean"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_EXECUTION_RESULT_REVIEW_20260719_v1.json"
)

TARGET = "review_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v1_execution_result"
VERDICT = "ACCEPTED_EXPLORATORY_IMPLEMENTATION_COMPLETED_WITH_RECORDED_FAILURES"
PRINCIPAL_OUTCOME = "VALIDATION_INFRASTRUCTURE_CHILD_PIPE_TRANSFER_FAILED_BEFORE_ADJUDICATION"
SECONDARY_OUTCOMES = (
    "MUTATION_HARNESS_WINDOWS_PLATFORM_PORTABILITY_DEFECT_LOCALIZED",
    "PRIMARY_NUMERICAL_AND_INTERFACE_OBSERVATIONS_PRESERVED",
    "KERNEL_QUALIFICATION_REMAINS_UNRESOLVED",
)
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_"
    "v1_execution_result_review_scientific_response_v0"
)

FROZEN_ARTIFACT_HASHES = {
    RESULT_RELATIVE_PATH: "3a6bc5738f774668c3d1387d7557d0c0654bb0db2a875f0237b655f539dec4ee",
    SIDECAR_RELATIVE_PATH: "35ec83791117b22dab1138c671d7ab5902a45650b4b42cab3d141062ed492b76",
    MARKER_RELATIVE_PATH: "2213b473aa598dbcbe0e161c0ba073cafef6775db82422115ceb8bf45cabb53a",
    STAGES_RELATIVE_PATH: "da924eaf4f7ddfea4f1efe69be11f15a809e8be69ac293eb5911c5524131cf6c",
    LOG_RELATIVE_PATH: "8ee1fbaa7fb9d0a4ab599807599d245586bad486df517c09ff12357487b71290",
    SOURCE_RELATIVE_PATH: "ebadb20d9a256af4251e488c0fc010e30cd90510de7b373191147f085fed1eca",
    V0_SOURCE_RELATIVE_PATH: "27a32f540465ed78cb2094629033a4aa30e3142c1f75aa113fc88eb10c7563ae",
    HUMAN_RESULT_RELATIVE_PATH: "66458c40d00291d55e01a4e7ae3aec6a7c9f542c8945496948af021b95dc17f1",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"{relative_path}: expected object")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _child_payload(row: dict[str, Any]) -> dict[str, Any]:
    payload = json.loads(row["stdout_ascii"])
    if not isinstance(payload, dict):
        raise TypeError("child payload must be an object")
    return payload


def _assert_frozen_custody() -> None:
    for relative_path, expected in FROZEN_ARTIFACT_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"frozen artifact drift: {relative_path}: {observed}")


def build_report() -> dict[str, Any]:
    _assert_frozen_custody()
    result = _load(RESULT_RELATIVE_PATH)
    marker = _load(MARKER_RELATIVE_PATH)
    stage_file = _load(STAGES_RELATIVE_PATH)
    source_text = (REPO_ROOT / V0_SOURCE_RELATIVE_PATH).read_text(encoding="utf-8")

    if result["terminal_outcome"] != "EXPLORATORY_IMPLEMENTATION_COMPLETED_WITH_RECORDED_FAILURES":
        raise ValueError("unexpected terminal outcome")
    if result["result_labels"] != [
        "EXPLORATORY_IMPLEMENTATION_RESULT",
        "NON_PRODUCTION",
        "NON_ADJUDICATIVE",
        "NO_SCIENTIFIC_CLAIM",
    ]:
        raise ValueError("nonclaim labels drift")
    if result["execution_count"] != 1 or result["authority_consumed"] is not True:
        raise ValueError("one-shot authority custody failed")
    if marker["run_id"] != result["run_id"]:
        raise ValueError("run identity mismatch")
    if marker["authority"] != (
        "execute_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v1_once"
    ):
        raise ValueError("authority marker mismatch")
    if marker["status"] != "CONSUMED_BY_SINGLE_LAUNCH_NO_RERUN":
        raise ValueError("authority-consumption status mismatch")
    if marker["source_sha256"] != FROZEN_ARTIFACT_HASHES[SOURCE_RELATIVE_PATH]:
        raise ValueError("source hash marker mismatch")

    stages = stage_file["stages"]
    if stages != result["stages"] or len(stages) != 8:
        raise ValueError("stage checkpoint mismatch")
    if not all(row["status"] == "COMPLETE" for row in stages):
        raise ValueError("incomplete stage checkpoint")
    if result["completeness"]["all_required_records_complete"] is not True:
        raise ValueError("required records incomplete")

    controls = {row["control_id"]: row for row in result["infrastructure"]["control_rows"]}
    c12 = controls["C12_CANONICAL_ROUND_TRIP_BYTES_AND_SHA256_STABLE"]
    required_c12 = (
        c12["passed"],
        c12["schema_complete_final_aggregate"],
        c12["actual_nested_adjudication_record_exercised"],
        c12["strict_schema_validation_passed"],
        c12["atomic_write_and_postwrite_verification_passed"],
        c12["bytes_identical"],
        c12["decimal_count_before_normalization"] == 2,
        c12["decimal_count_after_normalization"] == 0,
    )
    if not all(required_c12):
        raise ValueError("canonical preservation control did not pass exactly")

    positive_surfaces = {
        "interface": result["interface"]["passed"],
        "regressions": result["regressions"]["passed"],
        "derivative_references": result["derivative_reference_performance"]["passed"],
        "boundary_and_limits": result["boundary_and_limits"]["passed"],
        "evaluator_overlap": result["boundary_and_limits"]["evaluator_overlap"]["passed"],
        "runtime": result["runtime"]["passed"],
    }
    if not all(positive_surfaces.values()):
        raise ValueError("preserved positive surface mismatch")
    if result["regressions"]["case_count_completed"] != 8:
        raise ValueError("regression count mismatch")
    if result["boundary_and_limits"]["probe_count_completed"] != 13:
        raise ValueError("boundary count mismatch")
    if result["runtime"]["trial_count"] != 5:
        raise ValueError("runtime trial count mismatch")

    synthetic_rows = result["infrastructure"]["mutation_route_rows"]
    kernel_rows = result["mutations"]["rows"]
    all_children = synthetic_rows + kernel_rows
    if len(synthetic_rows) != 8 or len(kernel_rows) != 12 or len(all_children) != 20:
        raise ValueError("mutation child count mismatch")
    parsed_failures: list[dict[str, Any]] = []
    for row in all_children:
        payload = _child_payload(row)
        child_error = payload.get("child_error")
        traceback_ascii = payload.get("traceback_ascii", "")
        if row["passed"] is not False or row["returncode"] != 1:
            raise ValueError("mutation child did not fail closed")
        if child_error != {
            "message": "[Errno 9] Bad file descriptor",
            "type": "builtins.OSError",
        }:
            raise ValueError("mutation child failure fingerprint mismatch")
        for token in ("_child_main", "_frame_read", "os.read(fd", "OSError: [Errno 9]"):
            if token not in traceback_ascii:
                raise ValueError(f"missing pre-adjudication traceback token: {token}")
        for forbidden in ("_synthetic_route_child(", "_kernel_mutation_child("):
            if forbidden in traceback_ascii:
                raise ValueError("trace entered a mutation adjudication function")
        parsed_failures.append(
            {
                "child_id": row["child_id"],
                "child_kind": row["child_kind"],
                "returncode": row["returncode"],
                "error_type": child_error["type"],
                "error_message": child_error["message"],
                "failure_boundary": "FIRST_CHILD_CAPABILITY_PIPE_READ",
                "candidate_or_predicate_entered": False,
            }
        )
    if controls["C08_ALL_EIGHT_MUTATION_ROUTES_DETECT"]["passed"] is not False:
        raise ValueError("mandatory synthetic mutation control unexpectedly passed")
    if result["infrastructure"]["passed"] is not False or result["mutations"]["passed"] is not False:
        raise ValueError("fail-closed precedence mismatch")

    launch_tokens = (
        "read_fd, write_fd = os.pipe()",
        "os.set_inheritable(read_fd, True)",
        '"--read-fd"',
        "str(read_fd)",
        "close_fds=False",
        "manifest, secret, _ = _frame_read(read_fd)",
    )
    if not all(token in source_text for token in launch_tokens):
        raise ValueError("static child-pipe launch trace incomplete")
    if not str(result["administrative"]["platform"]).startswith("Windows-"):
        raise ValueError("observed platform is not Windows")

    review_gates = (
        ("E01_RESULT_HASH", "canonical result hash exact"),
        ("E02_SIDECAR_HASH", "hash sidecar frozen"),
        ("E03_AUTHORITY_MARKER_HASH", "authority marker frozen"),
        ("E04_STAGE_CHECKPOINT_HASH", "stage checkpoint frozen"),
        ("E05_RAW_LOG_HASH", "raw log frozen"),
        ("E06_V1_SOURCE_HASH", "executed V1 source frozen"),
        ("E07_HUMAN_HANDOFF_HASH", "execution handoff frozen"),
        ("E08_ONE_SHOT_AUTHORITY", "exactly one launch consumed"),
        ("E09_RUN_IDENTITY", "result and marker run IDs agree"),
        ("E10_NO_RERUN_STATUS", "marker forbids rerun"),
        ("E11_EIGHT_STAGES", "all eight stage boundaries complete"),
        ("E12_COMPLETE_RECORD_SET", "all required records preserved"),
        ("E13_SERIALIZATION_CONTROL", "actual aggregate serialization passed"),
        ("E14_DECIMAL_NORMALIZATION", "nested Decimal normalization exact"),
        ("E15_ATOMIC_PRESERVATION", "atomic write and verification passed"),
        ("E16_INTERFACE_OBSERVATION", "interface checks preserved as passing"),
        ("E17_REGRESSION_OBSERVATION", "eight regressions preserved as passing"),
        ("E18_DERIVATIVE_OBSERVATION", "derivative references preserved as passing"),
        ("E19_BOUNDARY_OBSERVATION", "thirteen boundary probes preserved as passing"),
        ("E20_OVERLAP_OBSERVATION", "six evaluator overlaps preserved as passing"),
        ("E21_RUNTIME_OBSERVATION", "runtime workload preserved as passing"),
        ("E22_EIGHT_SYNTHETIC_CHILDREN", "all synthetic child records present"),
        ("E23_TWELVE_KERNEL_CHILDREN", "all kernel child records present"),
        ("E24_COMMON_ERROR_TYPE", "all twenty errors are builtins.OSError"),
        ("E25_COMMON_ERROR_MESSAGE", "all twenty report bad file descriptor"),
        ("E26_FIRST_CHILD_READ_BOUNDARY", "all traces fail on first pipe read"),
        ("E27_SESSION_NOT_CONSTRUCTED", "validation session construction not reached"),
        ("E28_FIXTURE_NOT_LOADED", "fixture loading not reached"),
        ("E29_MUTATION_NOT_INJECTED", "mutation injection not reached"),
        ("E30_CANDIDATE_NOT_CALLED", "candidate mutation call not reached"),
        ("E31_PREDICATE_NOT_RUN", "mutation predicate not reached"),
        ("E32_ADJUDICATION_NOT_RUN", "mutation adjudication not reached"),
        ("E33_WINDOWS_PLATFORM", "failure observed on frozen Windows platform"),
        ("E34_PIPE_TRANSFER_LOCALIZED", "numeric descriptor invalid in child"),
        ("E35_PORTABILITY_ATTRIBUTION", "harness platform-portability defect localized"),
        ("E36_FAIL_CLOSED_PRECEDENCE", "mandatory failures suppress qualification"),
        ("E37_NONCLAIM_LABELS", "four nonclaim labels preserved"),
        ("E38_NO_KERNEL_INFERENCE", "kernel remains neither qualified nor refuted"),
        ("E39_DOWNSTREAM_FIREWALLS", "production and scientific work remain closed"),
        ("E40_SELECTOR_ONLY", "review rotates only to fresh response selector"),
    )

    scope = {
        "independent_execution_result_review_performed": True,
        "one_shot_custody_accepted": True,
        "canonical_preservation_pass_accepted": True,
        "bounded_positive_exploratory_observations_accepted": True,
        "validation_infrastructure_child_pipe_failure_accepted": True,
        "windows_mutation_harness_portability_defect_localized": True,
        "mutation_adjudication_completed": False,
        "validation_infrastructure_qualified": False,
        "analytic_kernel_qualified": False,
        "analytic_kernel_refuted": False,
        "historical_cubature_adjudicated": False,
        "implementation_edit_authorized": False,
        "pipe_repair_authorized": False,
        "sandbox_rerun_authorized": False,
        "sandbox_v2_authorized": False,
        "additional_prerequisite_authorized": False,
        "production_change_authorized": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
        "fresh_scientific_response_selector_authorized": True,
    }

    return {
        "schema_id": (
            "toe.scalar_only_yukawa.analytic_sphere_kernel.exploratory_sandbox_"
            "execution_result_review.v1"
        ),
        "review_id": (
            "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_"
            "EXECUTION_RESULT_REVIEW_20260719_v1"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_review_outcome": PRINCIPAL_OUTCOME,
        "secondary_review_outcomes": list(SECONDARY_OUTCOMES),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "FRESH_TERMINAL_CONSTRAINT_SCIENTIFIC_RESPONSE_SELECTOR",
        "authority": {
            "consumed_execution_outcome": result["terminal_outcome"],
            "frozen_execution_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in FROZEN_ARTIFACT_HASHES.items()
            ],
            "human_review": _artifact_row(HUMAN_REVIEW_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
                "exploratory_sandbox_execution_result_review_v1.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "custody_review": {
            "run_id": result["run_id"],
            "authorized_execution_count": 1,
            "consumed_execution_count": 1,
            "surviving_process_count": 0,
            "completed_stage_boundary_count": 8,
            "all_required_records_preserved": True,
            "canonical_result_written_and_verified": True,
            "source_frozen_after_execution": True,
        },
        "preserved_exploratory_observations": {
            "status": "BOUNDED_NONQUALIFYING_POSITIVE_OBSERVATIONS",
            "surfaces": positive_surfaces,
            "regression_case_count": 8,
            "derivative_reference_case_count": 8,
            "boundary_probe_count": 13,
            "evaluator_overlap_count": 6,
            "runtime_trial_count": 5,
            "median_10000_call_duration_ns": result["runtime"]["median_duration_ns"],
            "qualifies_kernel": False,
        },
        "mutation_failure_review": {
            "synthetic_route_count": 8,
            "kernel_mutation_count": 12,
            "total_child_failure_count": 20,
            "common_error_type": "builtins.OSError",
            "common_error_message": "[Errno 9] Bad file descriptor",
            "common_failure_boundary": "FIRST_CHILD_CAPABILITY_PIPE_READ",
            "platform": result["administrative"]["platform"],
            "validation_session_constructed": False,
            "fixture_loaded": False,
            "mutation_injected": False,
            "candidate_called": False,
            "predicate_executed": False,
            "adjudication_executed": False,
            "rows": parsed_failures,
        },
        "defect_attribution": {
            "principal_classification": "VALIDATION_INFRASTRUCTURE_IMPLEMENTATION_FAILURE",
            "secondary_classification": "MUTATION_HARNESS_WINDOWS_PLATFORM_PORTABILITY_DEFECT",
            "proven_boundary": (
                "THE_CHILD_PROCESS_DID_NOT_POSSESS_A_VALID_NUMERIC_FILE_DESCRIPTOR_"
                "FOR_THE_PARENT_CAPABILITY_PIPE"
            ),
            "further_mechanism_adjudicated": False,
            "possible_unadjudicated_mechanisms": [
                "WINDOWS_CRT_DESCRIPTOR_MAPPING",
                "OS_HANDLE_INHERITANCE_CONFIGURATION",
                "COMBINATION_OF_BOTH",
            ],
            "candidate_kernel_defect_established": False,
            "scientific_mutation_disagreement_established": False,
        },
        "scientific_admissibility": {
            "canonical_preservation": "PASSED",
            "primary_numerical_and_interface_rows": "PRESERVED_EXPLORATORY_OBSERVATIONS",
            "mandatory_mutation_controls": "FAILED_BEFORE_ADJUDICATION",
            "kernel_pass_or_fail": "UNRESOLVED",
            "validation_infrastructure": "NOT_QUALIFIED",
            "historical_cubature": "UNADJUDICATED",
            "scientific_claim": "NONE",
        },
        "review_gates": {
            "gate_count": len(review_gates),
            "pass_count": len(review_gates),
            "failure_count": 0,
            "rows": [
                {"gate_id": gate_id, "status": "PASS", "finding": finding}
                for gate_id, finding in review_gates
            ],
        },
        "scope": scope,
        "next_response_boundary": {
            "automatic_rerun": "PROHIBITED",
            "direct_pipe_repair_and_rerun": "PROHIBITED",
            "sandbox_v2": "PROHIBITED",
            "additional_prerequisite": "PROHIBITED",
            "production_or_scientific_advance": "PROHIBITED",
            "fresh_selector_required": True,
            "retire_or_defer_available": True,
            "separately_governed_nonrerun_use_of_preserved_observations_may_be_selected": True,
        },
        "claim_ceiling": (
            "This review accepts complete V1 custody, the canonical-preservation pass, and "
            "bounded positive exploratory observations. It localizes a Windows child-pipe "
            "transfer failure in the mandatory mutation harness before adjudication. It does "
            "not qualify or refute the analytic kernel, adjudicate cubature, authorize a pipe "
            "repair or rerun, change production, rerun Stage A, compute torque, DFT, vector, "
            "Jacobian, SVD, or identifiability, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Review the final one-shot analytic sphere-kernel sandbox V1 result."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    output = REPO_ROOT / REPORT_RELATIVE_PATH
    expected = artifact_bytes()
    current = output.read_bytes() if output.exists() else None
    if args.write:
        if current != expected:
            output.write_bytes(expected)
            print(f"wrote {REPORT_RELATIVE_PATH}")
        else:
            print("exploratory sandbox V1 execution-result review already current")
        return 0
    if current != expected:
        print("exploratory sandbox V1 execution-result review drift")
        return 1
    report = build_report()
    print(
        "exploratory sandbox V1 execution-result review OK "
        f"verdict={report['verdict']} gates={report['review_gates']['pass_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
