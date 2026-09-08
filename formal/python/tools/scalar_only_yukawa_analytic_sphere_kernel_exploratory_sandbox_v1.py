from __future__ import annotations

import hashlib
import json
import math
import os
import sys
import tempfile
import uuid
from decimal import Decimal, localcontext
from pathlib import Path
from typing import Any, Callable

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal.python.tools import (
    scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v0 as base,
)


SOURCE_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v1.py"
)
V0_SOURCE_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v0.py"
)
V0_SOURCE_SHA256 = "27a32f540465ed78cb2094629033a4aa30e3142c1f75aa113fc88eb10c7563ae"
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_V0_EXECUTION_RESULT_REVIEW_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.json"
)
SELECTOR_SHA256 = "f8a9fb6ce2f11a4b19247f2a61a3bfeebddf9d121856a6c082aeaa36e3dbda35"
RESULT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v1.json"
)
RESULT_SHA_RELATIVE_PATH = RESULT_RELATIVE_PATH + ".sha256"
RAW_LOG_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v1.log"
)
STAGE_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v1.stages.json"
)
CONSUMPTION_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v1.authority_consumed.json"
)
V1_AUTHORITY = (
    "execute_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v1_once"
)
V0_RESULT_SCHEMA_ID = (
    "toe.scalar_only_yukawa.analytic_sphere_kernel.exploratory_sandbox_result.v0"
)
V1_RESULT_SCHEMA_ID = (
    "toe.scalar_only_yukawa.analytic_sphere_kernel.exploratory_sandbox_result.v1"
)
V0_CONSUMPTION_SCHEMA_ID = (
    "toe.scalar_only_yukawa.analytic_sphere_kernel."
    "exploratory_sandbox_authority_consumption.v0"
)
V1_CONSUMPTION_SCHEMA_ID = (
    "toe.scalar_only_yukawa.analytic_sphere_kernel."
    "exploratory_sandbox_authority_consumption.v1"
)

FINAL_TOP_LEVEL_KEYS = {
    "schema_id",
    "result_labels",
    "run_id",
    "authority_consumed",
    "execution_count",
    "implementation",
    "infrastructure",
    "interface",
    "regressions",
    "derivative_reference_performance",
    "boundary_and_limits",
    "mutations",
    "runtime",
    "administrative",
    "stages",
    "terminal_outcome",
    "claim_ceiling",
    "completeness",
}
SECTION_KEYS = (
    "implementation",
    "infrastructure",
    "interface",
    "regressions",
    "derivative_reference_performance",
    "boundary_and_limits",
    "mutations",
    "runtime",
    "administrative",
    "completeness",
)
STAGE_IDS = (
    "S01_AUTHORITY_AND_CONTRACT_CUSTODY",
    "S02_VALIDATION_INFRASTRUCTURE_AND_SYNTHETIC_CONTROLS",
    "S03_INTERFACE_AND_PRIVATE_HOOK_ISOLATION",
    "S04_EIGHT_FROZEN_ENERGY_AND_DERIVATIVE_REGRESSIONS",
    "S05_EVALUATOR_OVERLAP_PROBES",
    "S06_THIRTEEN_BOUNDARY_AND_LIMIT_PROBES",
    "S07_TWELVE_ISOLATED_KERNEL_MUTATIONS",
    "S08_FROZEN_RUNTIME_WORKLOAD",
)
TERMINAL_OUTCOMES = {
    "EXPLORATORY_IMPLEMENTATION_INCOMPLETE",
    "EXPLORATORY_IMPLEMENTATION_COMPLETED_ALL_CONTROLS_PASS",
    "EXPLORATORY_IMPLEMENTATION_COMPLETED_WITH_RECORDED_FAILURES",
    "EXPLORATORY_IMPLEMENTATION_FAILED_OR_INCOMPLETE",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_decimal(value: Decimal) -> str:
    if not value.is_finite():
        raise base.SchemaValidationError("NONFINITE_DECIMAL")
    if value.is_zero():
        return "0"
    precision = max(50, len(value.as_tuple().digits))
    with localcontext() as context:
        context.prec = precision
        return str(value.normalize(context)).upper()


def _normalize_canonical(value: Any, pointer: str = "") -> Any:
    if isinstance(value, Decimal):
        return _canonical_decimal(value)
    if value is None or isinstance(value, (str, bool)):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            raise base.SchemaValidationError(f"{pointer or '/'}:NONFINITE")
        return value
    if isinstance(value, dict):
        normalized: dict[str, Any] = {}
        for key, child in value.items():
            if not isinstance(key, str):
                raise base.SchemaValidationError(f"{pointer or '/'}:NONSTRING_KEY")
            child_pointer = f"{pointer}/{key}" if pointer else f"/{key}"
            normalized[key] = _normalize_canonical(child, child_pointer)
        return normalized
    if isinstance(value, (list, tuple)):
        return [
            _normalize_canonical(child, f"{pointer}/{index}" if pointer else f"/{index}")
            for index, child in enumerate(value)
        ]
    raise base.SchemaValidationError(
        f"{pointer or '/'}:UNEXPECTED_TYPE:{type(value).__module__}.{type(value).__qualname__}"
    )


def _upgrade_v1_identifiers(value: Any) -> Any:
    if not isinstance(value, dict):
        return value
    schema_id = value.get("schema_id")
    if schema_id == V0_RESULT_SCHEMA_ID:
        upgraded = dict(value)
        upgraded["schema_id"] = V1_RESULT_SCHEMA_ID
        return upgraded
    if schema_id == V0_CONSUMPTION_SCHEMA_ID:
        upgraded = dict(value)
        upgraded["schema_id"] = V1_CONSUMPTION_SCHEMA_ID
        upgraded["authority"] = V1_AUTHORITY
        return upgraded
    return value


def _validate_canonical_tree(value: Any, pointer: str = "") -> None:
    if value is None or isinstance(value, (str, bool)):
        return
    if isinstance(value, int) and not isinstance(value, bool):
        return
    if isinstance(value, float):
        if not math.isfinite(value):
            raise base.SchemaValidationError(f"{pointer or '/'}:NONFINITE")
        return
    if isinstance(value, dict):
        for key, child in value.items():
            if not isinstance(key, str):
                raise base.SchemaValidationError(f"{pointer or '/'}:NONSTRING_KEY")
            child_pointer = f"{pointer}/{key}" if pointer else f"/{key}"
            _validate_canonical_tree(child, child_pointer)
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _validate_canonical_tree(
                child, f"{pointer}/{index}" if pointer else f"/{index}"
            )
        return
    raise base.SchemaValidationError(
        f"{pointer or '/'}:NONCANONICAL_TYPE:{type(value).__module__}.{type(value).__qualname__}"
    )


def _validate_final_result_schema(value: dict[str, Any]) -> None:
    if set(value) != FINAL_TOP_LEVEL_KEYS:
        missing = sorted(FINAL_TOP_LEVEL_KEYS - set(value))
        unknown = sorted(set(value) - FINAL_TOP_LEVEL_KEYS)
        raise base.SchemaValidationError(
            f"FINAL_RESULT_SCHEMA_KEYS:missing={missing}:unknown={unknown}"
        )
    if value["schema_id"] != V1_RESULT_SCHEMA_ID:
        raise base.SchemaValidationError("FINAL_RESULT_SCHEMA_ID")
    if value["result_labels"] != list(base.EXPLORATORY_LABELS):
        raise base.SchemaValidationError("FINAL_RESULT_LABELS")
    try:
        parsed_run_id = uuid.UUID(value["run_id"])
    except (ValueError, TypeError, AttributeError) as exc:
        raise base.SchemaValidationError("FINAL_RESULT_RUN_ID") from exc
    if parsed_run_id.version != 4 or str(parsed_run_id) != value["run_id"]:
        raise base.SchemaValidationError("FINAL_RESULT_RUN_ID")
    if value["authority_consumed"] is not True or value["execution_count"] != 1:
        raise base.SchemaValidationError("FINAL_RESULT_AUTHORITY_OR_EXECUTION_COUNT")
    for key in SECTION_KEYS:
        if not isinstance(value[key], dict):
            raise base.SchemaValidationError(f"FINAL_RESULT_SECTION_TYPE:{key}")
    if not isinstance(value["stages"], list):
        raise base.SchemaValidationError("FINAL_RESULT_STAGES_TYPE")
    observed_stage_ids: list[str] = []
    for row in value["stages"]:
        if not isinstance(row, dict):
            raise base.SchemaValidationError("FINAL_RESULT_STAGE_ROW_TYPE")
        if not {"stage_id", "status", "duration_ns"}.issubset(row):
            raise base.SchemaValidationError("FINAL_RESULT_STAGE_ROW_FIELDS")
        if row["stage_id"] not in STAGE_IDS or row["status"] not in ("COMPLETE", "FAILED"):
            raise base.SchemaValidationError("FINAL_RESULT_STAGE_ROW_ENUM")
        if not isinstance(row["duration_ns"], int) or isinstance(row["duration_ns"], bool):
            raise base.SchemaValidationError("FINAL_RESULT_STAGE_DURATION")
        observed_stage_ids.append(row["stage_id"])
    if observed_stage_ids != list(STAGE_IDS[: len(observed_stage_ids)]):
        raise base.SchemaValidationError("FINAL_RESULT_STAGE_ORDER")
    if value["terminal_outcome"] not in TERMINAL_OUTCOMES:
        raise base.SchemaValidationError("FINAL_RESULT_TERMINAL_OUTCOME")
    if not isinstance(value["claim_ceiling"], str) or not value["claim_ceiling"]:
        raise base.SchemaValidationError("FINAL_RESULT_CLAIM_CEILING")
    required_completeness = {
        "implementation_complete",
        "infrastructure_controls_completed",
        "infrastructure_controls_required",
        "regression_cases_completed",
        "regression_cases_required",
        "boundary_probes_completed",
        "boundary_probes_required",
        "kernel_mutations_completed",
        "kernel_mutations_required",
        "runtime_trials_completed",
        "runtime_trials_required",
        "all_required_records_complete",
    }
    if set(value["completeness"]) != required_completeness:
        raise base.SchemaValidationError("FINAL_RESULT_COMPLETENESS_FIELDS")
    _validate_canonical_tree(value)


def _canonical_bytes_v1(value: Any) -> bytes:
    normalized = _upgrade_v1_identifiers(_normalize_canonical(value))
    _validate_canonical_tree(normalized)
    if isinstance(normalized, dict) and normalized.get("schema_id") == V1_RESULT_SCHEMA_ID:
        _validate_final_result_schema(normalized)
    return (
        json.dumps(
            normalized,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _verify_json_payload(payload: bytes) -> tuple[Any, str]:
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise base.SchemaValidationError("CANONICAL_UTF8_REQUIRED") from exc
    parsed = base.loads_strict(text)
    _validate_canonical_tree(parsed)
    if isinstance(parsed, dict) and parsed.get("schema_id") == V1_RESULT_SCHEMA_ID:
        _validate_final_result_schema(parsed)
    if _canonical_bytes_v1(parsed) != payload:
        raise base.SchemaValidationError("NONCANONICAL_ROUND_TRIP_BYTES")
    return parsed, hashlib.sha256(payload).hexdigest()


def _atomic_write_verified(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    is_json = path.name.endswith(".json")
    expected_digest = hashlib.sha256(payload).hexdigest()
    if is_json:
        _, verified_digest = _verify_json_payload(payload)
        if verified_digest != expected_digest:
            raise base.SchemaValidationError("PREWRITE_HASH_MISMATCH")
    fd, temporary_name = tempfile.mkstemp(
        prefix=path.name + ".", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        temporary_payload = temporary.read_bytes()
        if temporary_payload != payload:
            raise base.SchemaValidationError("TEMPORARY_FILE_BYTE_MISMATCH")
        if hashlib.sha256(temporary_payload).hexdigest() != expected_digest:
            raise base.SchemaValidationError("TEMPORARY_FILE_HASH_MISMATCH")
        if is_json:
            _verify_json_payload(temporary_payload)
        os.replace(temporary, path)
        canonical_payload = path.read_bytes()
        if canonical_payload != payload:
            raise base.SchemaValidationError("CANONICAL_FILE_BYTE_MISMATCH")
        if hashlib.sha256(canonical_payload).hexdigest() != expected_digest:
            raise base.SchemaValidationError("CANONICAL_FILE_HASH_MISMATCH")
        if is_json:
            _verify_json_payload(canonical_payload)
    finally:
        if temporary.exists():
            temporary.unlink()


def _count_instances(value: Any, target_type: type[Any]) -> int:
    if isinstance(value, target_type):
        return 1
    if isinstance(value, dict):
        return sum(_count_instances(child, target_type) for child in value.values())
    if isinstance(value, (list, tuple)):
        return sum(_count_instances(child, target_type) for child in value)
    return 0


def _synthetic_final_aggregate() -> dict[str, Any]:
    predicate = {
        "predicate_id": "P_V1_REAL_PATH_DECIMAL",
        "kind": "NUMERIC",
        "observed_pointer": "/observed",
        "reference_pointer": "/reference",
        "reference_decimal": None,
        "absolute_tolerance_decimal": "1E-30",
        "relative_tolerance_decimal": "1E-12",
        "comparator": "ABS_REL_LE",
    }
    adjudication = base.adjudicate_v0(
        predicate,
        {"observed": float(1.25).hex(), "reference": float(1.25).hex()},
    )
    stages = [
        {"stage_id": stage_id, "status": "COMPLETE", "duration_ns": index + 1}
        for index, stage_id in enumerate(STAGE_IDS)
    ]
    return {
        "schema_id": V0_RESULT_SCHEMA_ID,
        "result_labels": list(base.EXPLORATORY_LABELS),
        "run_id": "00000000-0000-4000-8000-000000000001",
        "authority_consumed": True,
        "execution_count": 1,
        "implementation": {
            "status": "COMPLETE",
            "source_relative_path": SOURCE_RELATIVE_PATH,
            "source_sha256": "0" * 64,
            "production_import_or_dispatch": False,
            "historical_cubature_called": False,
            "source_dependency_scan": {},
            "contract_hashes": {},
        },
        "infrastructure": {
            "status": "COMPLETE",
            "control_count_expected": 12,
            "control_count_completed": 12,
            "control_rows": [{
                "control_id": "C07_NUMERIC_RELATIONAL_AND_EXCEPTION_PREDICATES_DETECT",
                "predicate_results": [adjudication],
                "passed": True,
            }],
            "mutation_route_rows": [],
            "duration_ns": 1,
            "within_60_second_bound": True,
            "passed": True,
        },
        "interface": {"status": "COMPLETE", "checks": {}, "passed": True},
        "regressions": {
            "status": "COMPLETE",
            "case_count_expected": 8,
            "case_count_completed": 8,
            "rows": [],
            "passed": True,
        },
        "derivative_reference_performance": {
            "status": "COMPLETE",
            "case_count_completed": 8,
            "passed": True,
        },
        "boundary_and_limits": {
            "status": "COMPLETE",
            "probe_count_expected": 13,
            "probe_count_completed": 13,
            "rows": [],
            "evaluator_overlap": {"status": "COMPLETE", "rows": [], "passed": True},
            "passed": True,
        },
        "mutations": {
            "status": "COMPLETE",
            "mutation_count_expected": 12,
            "mutation_count_completed": 12,
            "rows": [],
            "passed": True,
        },
        "runtime": {
            "status": "COMPLETE",
            "warmup_call_count": 24,
            "trial_count": 5,
            "timed_call_count_per_trial": 10000,
            "trial_rows": [],
            "median_duration_ns": 1,
            "maximum_median_seconds": 5.0,
            "passed": True,
        },
        "administrative": {
            "automatic_retry_or_rerun": False,
            "downstream_scientific_execution": False,
        },
        "stages": stages,
        "terminal_outcome": "EXPLORATORY_IMPLEMENTATION_COMPLETED_ALL_CONTROLS_PASS",
        "claim_ceiling": "Synthetic schema-complete serialization control only.",
        "completeness": {
            "implementation_complete": True,
            "infrastructure_controls_completed": 12,
            "infrastructure_controls_required": 12,
            "regression_cases_completed": 8,
            "regression_cases_required": 8,
            "boundary_probes_completed": 13,
            "boundary_probes_required": 13,
            "kernel_mutations_completed": 12,
            "kernel_mutations_required": 12,
            "runtime_trials_completed": 5,
            "runtime_trials_required": 5,
            "all_required_records_complete": True,
        },
    }


def _serialization_controls_v1() -> tuple[dict[str, Any], dict[str, Any]]:
    checks: list[dict[str, Any]] = []

    def expect(
        name: str, operation: Callable[[], Any], expected_type: type[BaseException]
    ) -> None:
        observed = None
        try:
            operation()
        except Exception as exc:
            observed = type(exc).__name__
        checks.append({
            "case_id": name,
            "observed_exception": observed,
            "passed": observed == expected_type.__name__,
        })

    expect("DUPLICATE_KEY", lambda: base.loads_strict('{"a":1,"a":2}'), base.DuplicateKeyError)
    expect("NONFINITE", lambda: base.loads_strict('{"a":NaN}'), base.SchemaValidationError)
    expect("UNKNOWN_ENUM", lambda: base._validate_run_status("UNKNOWN"), base.SchemaValidationError)

    def validate_shape(value: dict[str, Any]) -> None:
        required = {"schema_id", "status"}
        missing = required - set(value)
        unknown = set(value) - required
        if missing:
            raise base.SchemaValidationError("MISSING_FIELD")
        if unknown:
            raise base.SchemaValidationError("UNKNOWN_FIELD")

    expect("MISSING_FIELD", lambda: validate_shape({"schema_id": "X"}), base.SchemaValidationError)
    expect(
        "UNKNOWN_FIELD",
        lambda: validate_shape({"schema_id": "X", "status": "COMPLETE", "extra": 1}),
        base.SchemaValidationError,
    )
    c11 = {
        "control_id": "C11_DUPLICATE_MISSING_UNKNOWN_NONFINITE_AND_ENUM_CASES_FAIL",
        "cases": checks,
        "passed": all(row["passed"] for row in checks),
    }

    aggregate = _synthetic_final_aggregate()
    decimal_count_before = _count_instances(aggregate, Decimal)
    normalized = _upgrade_v1_identifiers(_normalize_canonical(aggregate))
    decimal_count_after = _count_instances(normalized, Decimal)
    _validate_final_result_schema(normalized)
    payload = _canonical_bytes_v1(aggregate)
    with tempfile.TemporaryDirectory(prefix="toe-v1-real-aggregate-") as directory:
        control_path = Path(directory) / Path(RESULT_RELATIVE_PATH).name
        _atomic_write_verified(control_path, payload)
        preserved = control_path.read_bytes()
    parsed, digest = _verify_json_payload(preserved)
    predicate_result = parsed["infrastructure"]["control_rows"][0]["predicate_results"][0]
    observed_is_string = isinstance(predicate_result["observed_canonical"], str)
    reference_is_string = isinstance(predicate_result["reference_canonical"], str)
    bytes_identical = preserved == payload == _canonical_bytes_v1(parsed)
    c12 = {
        "control_id": "C12_CANONICAL_ROUND_TRIP_BYTES_AND_SHA256_STABLE",
        "canonical_sha256": digest,
        "schema_complete_final_aggregate": True,
        "actual_nested_adjudication_record_exercised": True,
        "decimal_count_before_normalization": decimal_count_before,
        "decimal_count_after_normalization": decimal_count_after,
        "observed_canonical_is_string": observed_is_string,
        "reference_canonical_is_string": reference_is_string,
        "strict_schema_validation_passed": True,
        "atomic_write_and_postwrite_verification_passed": True,
        "bytes_identical": bytes_identical,
        "passed": (
            decimal_count_before == 2
            and decimal_count_after == 0
            and observed_is_string
            and reference_is_string
            and bytes_identical
        ),
    }
    return c11, c12


def _install_v1_boundary() -> None:
    if _sha256(REPO_ROOT / V0_SOURCE_RELATIVE_PATH) != V0_SOURCE_SHA256:
        raise RuntimeError("V0_SANDBOX_SOURCE_HASH_DRIFT")
    if _sha256(REPO_ROOT / SELECTOR_RELATIVE_PATH) != SELECTOR_SHA256:
        raise RuntimeError("V1_SELECTOR_HASH_DRIFT")

    base.SOURCE_RELATIVE_PATH = SOURCE_RELATIVE_PATH
    base.RESULT_RELATIVE_PATH = RESULT_RELATIVE_PATH
    base.RESULT_SHA_RELATIVE_PATH = RESULT_SHA_RELATIVE_PATH
    base.RAW_LOG_RELATIVE_PATH = RAW_LOG_RELATIVE_PATH
    base.STAGE_RELATIVE_PATH = STAGE_RELATIVE_PATH
    base.CONSUMPTION_RELATIVE_PATH = CONSUMPTION_RELATIVE_PATH
    base.SELECTOR_RELATIVE_PATH = SELECTOR_RELATIVE_PATH
    base.EXPECTED_HASHES = {
        base.INFRA_RELATIVE_PATH: "66ce9cd50115963c531c31524e20e7c567692f5455f8b8bde5411bf685da4d12",
        base.KERNEL_RELATIVE_PATH: "cbd393070a567368a83327bd99e53dbb18013bba8ac9447cc7952b74a2d6c122",
        SELECTOR_RELATIVE_PATH: SELECTOR_SHA256,
        base.ORACLE_RELATIVE_PATH: "d2527fd3c03a107734b3b55920c35f73185cbbf0f6c13132ff94c40ec447676d",
        V0_SOURCE_RELATIVE_PATH: V0_SOURCE_SHA256,
    }
    base._canonical_bytes = _canonical_bytes_v1
    base._atomic_write = _atomic_write_verified
    base._serialization_controls = _serialization_controls_v1


def main() -> int:
    _install_v1_boundary()
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
