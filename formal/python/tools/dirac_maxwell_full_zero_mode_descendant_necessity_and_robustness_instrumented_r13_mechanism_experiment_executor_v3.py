from __future__ import annotations

"""Fail-closed runtime custody for the frozen R13 mechanism experiment.

Import is inert.  This module neither creates the experiment output directory
nor calls the evolution code.  Runtime authority can only come from the fixed,
accepted v3 independent-review anchor.  The execution entry point accepts no
matrix, record, authority, path, or run-order override.
"""

import copy
import hashlib
import importlib
import json
import math
import os
import platform
import sys
import unicodedata
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import Any

import numpy as np

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v3
    as custody,
)


EXECUTOR_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_EXECUTOR_v3"
)
PHYSICAL_CONFIGURATION_CORE_SCHEMA_ID = (
    "DIRAC_MAXWELL_R13_MECHANISM_PHYSICAL_CONFIGURATION_CORE_v2"
)
SCIENTIFIC_INPUT_CORE_SCHEMA_ID = (
    "DIRAC_MAXWELL_R13_MECHANISM_SCIENTIFIC_INPUT_CORE_v2"
)
FULL_RECORD_IDENTITY_SCHEMA_ID = (
    "DIRAC_MAXWELL_R13_MECHANISM_FULL_MATRIX_RECORD_IDENTITY_v3"
)
COMPLETE_EXECUTION_IDENTITY_SCHEMA_ID = (
    "DIRAC_MAXWELL_R13_MECHANISM_COMPLETE_EXECUTION_IDENTITY_v3"
)
PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID = (
    "DIRAC_MAXWELL_R13_MECHANISM_FROZEN_RUN_TEMPLATE_v3"
)
ROLE_RESOLUTION_OVERLAY_SCHEMA_ID = (
    "DIRAC_MAXWELL_R13_MECHANISM_ROLE_RESOLUTION_OVERLAY_v3"
)
RESOLVED_METRIC_CONFIGURATION_SCHEMA_ID = (
    "DIRAC_MAXWELL_R13_MECHANISM_RESOLVED_RUN_CONFIGURATION_v3"
)
RUNTIME_PREFLIGHT_SCHEMA_ID = "DIRAC_MAXWELL_R13_MECHANISM_RUNTIME_PREFLIGHT_v3"
EXECUTION_STARTED_SCHEMA_ID = "DIRAC_MAXWELL_R13_MECHANISM_EXECUTION_STARTED_v3"
MATRIX_RESULT_SCHEMA_ID = "DIRAC_MAXWELL_R13_MECHANISM_MATRIX_RESULT_v3"


class RuntimeCustodyError(RuntimeError):
    """Raised before evolution whenever exact runtime custody is not proved."""


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, Mapping):
        return {str(key): _normalize(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_normalize(item) for item in value]
    if isinstance(value, float) and not math.isfinite(value):
        raise ValueError("canonical JSON forbids nonfinite floats")
    return value


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


def sha256_bytes(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def _is_hex_digest(value: Any, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _required(record: Mapping[str, Any], names: Sequence[str]) -> None:
    missing = [name for name in names if name not in record]
    if missing:
        raise ValueError(f"record missing positive-inclusion field: {missing[0]}")


_PHYSICAL_FIELDS = (
    "accepted_step_count",
    "checkpoint_count_including_initial",
    "dt",
    "duration",
    "grid_size",
    "iteration_cap",
    "max_iterations",
    "model_class",
    "n",
    "numerical_method",
    "parent_canonical_input_hash",
    "parent_canonical_output_path",
    "parent_canonical_output_sha256",
    "parent_canonical_run_id",
    "parent_initial_condition_identity",
    "requested_axis_values",
    "row",
    "scientific_row_id",
    "solver_tolerance",
    "time_step",
    "tolerance",
)
_SCIENTIFIC_IDENTITY_FIELDS = (
    "classifier_id",
    "classifier_sha256",
    "execution_ordinal_zero_based",
    "execution_role",
    "executor_id",
    "executor_sha256",
    "experiment_id",
    "implementation_id",
    "implementation_sha256",
    "runtime_source_closure_sha256",
    "instrumentation_enabled",
    "instrumentation_read_only",
    "instrumented_observable_ids",
    "json_relative_output_path",
    "json_safe_filename",
    "mechanism_configuration_role",
    "npz_relative_output_path",
    "npz_safe_filename",
    "output_schema_version",
    "paired_run_id",
    "payload_identity_contract",
    "partial_metric_configuration_sha256",
    "raw_evidence_assembler_id",
    "raw_evidence_assembler_sha256",
    "run_id",
    "role_resolution_overlay_sha256",
    "semantic_contract_id",
    "semantic_contract_sha256",
    "supporting_duration_scaling_module_enabled",
    "supporting_tolerance_ladder_module_enabled",
    "resolved_metric_configuration_sha256",
    "trajectory_identity_required",
)

# Frozen diagnostic precedence for the exact twenty atomic identity controls.
IDENTITY_DIAGNOSTIC_FIELDS = (
    "parent_canonical_run_id",
    "parent_canonical_input_hash",
    "parent_canonical_output_sha256",
    "parent_canonical_output_path",
    "input_hash",
    "implementation_id",
    "implementation_sha256",
    "paired_run_id",
    "execution_role",
    "output_schema_version",
    "experiment_id",
    "scientific_row_id",
    "requested_axis_values",
    "parent_initial_condition_identity",
    "model_class",
    "numerical_method",
    "accepted_step_count",
    "checkpoint_count_including_initial",
    "instrumentation_read_only",
    "trajectory_identity_required",
)

METRIC_BLOCK_IDS = (
    "THETA_KINEMATIC",
    "P_LONGITUDINAL_MAXWELL",
    "PHI2_KINEMATIC",
    "P2_DYNAMIC",
    "PHI3_KINEMATIC",
    "P3_DYNAMIC",
    "DIRAC_PLUS",
    "DIRAC_MINUS",
)
GAMMA64 = 7.105427357601052e-15
PARTIAL_TEMPLATE_REQUIRED_FIELDS = {
    "block_floor_rule",
    "block_floors_materialized_by_execution_harness",
    "block_scale_rule",
    "block_scales_materialized_by_execution_harness",
    "distributed_effective_block_count_minimum",
    "distributed_effective_count_formula",
    "distributed_minimum_contributing_block_count",
    "distributed_per_block_share_minimum",
    "distributed_single_block_share_maximum_exclusive",
    "epsilon_dominance",
    "linked_structural_series",
    "no_posthoc_window_lag_exponent_or_point_selection",
    "postinitial_sample_count",
    "severe_kappa_threshold",
}


class ConfigurationResolutionError(RuntimeCustodyError):
    """Exact fail-closed diagnostic for frozen role resolution."""


def validate_partial_metric_configuration(
    partial: Mapping[str, Any],
) -> list[str]:
    if not isinstance(partial, Mapping):
        return ["PARTIAL_METRIC_CONFIGURATION_NOT_MAPPING"]
    if partial.get("schema_id") != PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID:
        return ["PARTIAL_METRIC_CONFIGURATION_SCHEMA_MISMATCH"]
    if not isinstance(partial.get("run_id"), str):
        return ["PARTIAL_METRIC_CONFIGURATION_RUN_ID_MISSING"]
    template = partial.get("metric_configuration_template")
    if not isinstance(template, Mapping):
        return ["PARTIAL_METRIC_CONFIGURATION_TEMPLATE_NOT_MAPPING"]
    if "block_floors" in template:
        return ["CALLER_SUPPLIED_METRIC_BLOCK_FLOORS_FORBIDDEN"]
    if "block_scales" in template:
        return ["CALLER_SUPPLIED_METRIC_BLOCK_SCALES_FORBIDDEN"]
    missing = sorted(PARTIAL_TEMPLATE_REQUIRED_FIELDS - set(template))
    if missing:
        return [f"PARTIAL_METRIC_CONFIGURATION_FIELD_MISSING:{missing[0]}"]
    if (
        template["block_floors_materialized_by_execution_harness"] is not True
        or template["block_scales_materialized_by_execution_harness"] is not True
    ):
        return ["PARTIAL_METRIC_CONFIGURATION_RESOLUTION_RULE_MISMATCH"]
    return []


def validate_role_resolution_overlay(
    record: Mapping[str, Any], overlay: Mapping[str, Any]
) -> list[str]:
    if not isinstance(overlay, Mapping):
        return ["ROLE_RESOLUTION_OVERLAY_NOT_MAPPING"]
    if overlay.get("schema_id") != ROLE_RESOLUTION_OVERLAY_SCHEMA_ID:
        return ["ROLE_RESOLUTION_OVERLAY_SCHEMA_MISMATCH"]
    if (
        overlay.get("run_id") != record.get("run_id")
        or overlay.get("execution_role") != record.get("execution_role")
        or overlay.get("instrumentation_enabled")
        != record.get("instrumentation_enabled")
        or overlay.get("requested_solver_tolerance") != record.get("tolerance")
    ):
        return ["ROLE_RESOLUTION_OVERLAY_IDENTITY_MISMATCH"]
    floors = overlay.get("block_floors")
    if not isinstance(floors, Mapping):
        return ["ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS"]
    expected_floors = {block_id: GAMMA64 for block_id in METRIC_BLOCK_IDS}
    if dict(floors) != expected_floors:
        return ["ROLE_RESOLUTION_WRONG_METRIC_BLOCK_FLOORS"]
    scales = overlay.get("block_scales")
    expected_scales = {
        block_id: float(record["tolerance"]) for block_id in METRIC_BLOCK_IDS
    }
    if not isinstance(scales, Mapping) or dict(scales) != expected_scales:
        return ["ROLE_RESOLUTION_WRONG_METRIC_BLOCK_SCALES"]
    if overlay.get("epsilon_dominance") != GAMMA64:
        return ["ROLE_RESOLUTION_WRONG_EPSILON_DOMINANCE"]
    return []


def validate_resolved_metric_configuration(
    record: Mapping[str, Any],
    resolved: Mapping[str, Any],
    overlay: Mapping[str, Any],
) -> list[str]:
    if not isinstance(resolved, Mapping):
        return ["RESOLVED_METRIC_CONFIGURATION_NOT_MAPPING"]
    if resolved.get("schema_id") == PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID:
        return ["UNRESOLVED_TEMPLATE_NOT_EXECUTABLE"]
    if resolved.get("schema_id") != RESOLVED_METRIC_CONFIGURATION_SCHEMA_ID:
        return ["RESOLVED_METRIC_CONFIGURATION_SCHEMA_MISMATCH"]
    if resolved.get("run_id") != record.get("run_id"):
        return ["RESOLVED_METRIC_CONFIGURATION_RUN_ID_MISMATCH"]
    metric = resolved.get("metric_configuration")
    if not isinstance(metric, Mapping):
        return ["RESOLVED_METRIC_CONFIGURATION_PAYLOAD_NOT_MAPPING"]
    if "block_floors" not in metric:
        return ["ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS"]
    expected_floors = {block_id: GAMMA64 for block_id in METRIC_BLOCK_IDS}
    if metric["block_floors"] != expected_floors:
        return ["ROLE_RESOLUTION_WRONG_METRIC_BLOCK_FLOORS"]
    expected_scales = {
        block_id: float(record["tolerance"]) for block_id in METRIC_BLOCK_IDS
    }
    if metric.get("block_scales") != expected_scales:
        return ["ROLE_RESOLUTION_WRONG_METRIC_BLOCK_SCALES"]
    if metric.get("epsilon_dominance") != GAMMA64:
        return ["ROLE_RESOLUTION_WRONG_EPSILON_DOMINANCE"]
    if resolved.get("role_resolution_overlay_sha256") != sha256_bytes(
        canonical_json_bytes(overlay)
    ):
        return ["ROLE_RESOLUTION_OVERLAY_IDENTITY_MISMATCH"]
    return []


def resolve_frozen_metric_configuration(
    record: Mapping[str, Any],
    partial: Mapping[str, Any],
    overlay: Mapping[str, Any],
) -> dict[str, Any]:
    diagnostics = validate_partial_metric_configuration(partial)
    if diagnostics:
        raise ConfigurationResolutionError(diagnostics[0])
    if partial["run_id"] != record.get("run_id"):
        raise ConfigurationResolutionError(
            "PARTIAL_METRIC_CONFIGURATION_RUN_ID_MISMATCH"
        )
    diagnostics = validate_role_resolution_overlay(record, overlay)
    if diagnostics:
        raise ConfigurationResolutionError(diagnostics[0])
    metric = copy.deepcopy(partial["metric_configuration_template"])
    metric["block_scales"] = copy.deepcopy(overlay["block_scales"])
    metric["block_floors"] = copy.deepcopy(overlay["block_floors"])
    metric["epsilon_dominance"] = overlay["epsilon_dominance"]
    resolved = {
        "schema_id": RESOLVED_METRIC_CONFIGURATION_SCHEMA_ID,
        "run_id": record["run_id"],
        "partial_metric_configuration_sha256": sha256_bytes(
            canonical_json_bytes(partial)
        ),
        "role_resolution_overlay_sha256": sha256_bytes(
            canonical_json_bytes(overlay)
        ),
        "metric_configuration": metric,
    }
    diagnostics = validate_resolved_metric_configuration(record, resolved, overlay)
    if diagnostics:
        raise ConfigurationResolutionError(diagnostics[0])
    return resolved


def build_read_only_execution_plan_record(
    record: Mapping[str, Any],
    configuration: Mapping[str, Any],
    overlay: Mapping[str, Any],
) -> dict[str, Any]:
    if configuration.get("schema_id") == PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID:
        raise ConfigurationResolutionError(
            "VALIDATION_BEFORE_ROLE_RESOLUTION_FORBIDDEN"
        )
    diagnostics = validate_resolved_metric_configuration(
        record, configuration, overlay
    )
    if diagnostics:
        raise ConfigurationResolutionError(diagnostics[0])
    return {
        "run_id": record["run_id"],
        "execution_role": record["execution_role"],
        "resolved_metric_configuration_sha256": sha256_bytes(
            canonical_json_bytes(configuration)
        ),
        "output_paths": {
            "json": record["json_relative_output_path"],
            "npz": record["npz_relative_output_path"],
        },
        "simulation_entered": False,
    }


def metric_configuration_for_numerical_execution(
    record: Mapping[str, Any],
    configuration: Mapping[str, Any],
    overlay: Mapping[str, Any],
) -> dict[str, Any]:
    if configuration.get("schema_id") == PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID:
        raise ConfigurationResolutionError(
            "PARTIAL_CONFIGURATION_NUMERICAL_EXECUTION_FORBIDDEN"
        )
    diagnostics = validate_resolved_metric_configuration(
        record, configuration, overlay
    )
    if diagnostics:
        raise ConfigurationResolutionError(diagnostics[0])
    return copy.deepcopy(configuration["metric_configuration"])


def build_physical_configuration_core(
    record: Mapping[str, Any], closure_digest: str
) -> dict[str, Any]:
    """Build the source-independent physical and numerical input core.

    ``closure_digest`` remains an explicit argument so callers cannot silently
    use an unvalidated runtime identity, but code identity is intentionally not
    included in this physics hash.
    """

    if not isinstance(record, Mapping):
        raise TypeError("record must be a mapping")
    if not _is_hex_digest(closure_digest, 64):
        raise ValueError("closure_digest must be a lowercase SHA-256")
    _required(record, _PHYSICAL_FIELDS)
    return {
        "schema_id": PHYSICAL_CONFIGURATION_CORE_SCHEMA_ID,
        "canonical_parent": {
            "run_id": record["parent_canonical_run_id"],
            "input_hash": record["parent_canonical_input_hash"],
            "output_path": record["parent_canonical_output_path"],
            "output_sha256": record["parent_canonical_output_sha256"],
            "initial_condition_identity": record[
                "parent_initial_condition_identity"
            ],
        },
        "physical_model": {
            "scientific_row_id": record["scientific_row_id"],
            "requested_axis_values": copy.deepcopy(
                record["requested_axis_values"]
            ),
            "row": copy.deepcopy(record["row"]),
            "model_class": record["model_class"],
        },
        "numerical_configuration": {
            "numerical_method": record["numerical_method"],
            "grid_size": record["grid_size"],
            "n": record["n"],
            "time_step": record["time_step"],
            "dt": record["dt"],
            "duration": record["duration"],
            "solver_tolerance": record["solver_tolerance"],
            "tolerance": record["tolerance"],
            "iteration_cap": record["iteration_cap"],
            "max_iterations": record["max_iterations"],
            "accepted_step_count": record["accepted_step_count"],
            "checkpoint_count_including_initial": record[
                "checkpoint_count_including_initial"
            ],
        },
    }


def build_scientific_input_core(
    record: Mapping[str, Any], closure_digest: str
) -> dict[str, Any]:
    """Build the positive-inclusion scientific-input identity.

    Instrumented/control pairs intentionally share this identity because they
    solve the same physical and numerical problem. Runtime and role identity
    are frozen separately in ``build_complete_execution_identity_core``.
    """

    _required(record, _SCIENTIFIC_IDENTITY_FIELDS)
    if record["runtime_source_closure_sha256"] != closure_digest:
        raise ValueError("record runtime source closure does not match authority")
    physical_core = build_physical_configuration_core(record, closure_digest)
    return {
        "schema_id": SCIENTIFIC_INPUT_CORE_SCHEMA_ID,
        "physical_configuration_core": physical_core,
    }


def build_complete_execution_identity_core(
    record: Mapping[str, Any], closure_digest: str
) -> dict[str, Any]:
    """Combine scientific, runtime, role, schema, and output identities."""

    _required(record, _SCIENTIFIC_IDENTITY_FIELDS)
    scientific_core = build_scientific_input_core(record, closure_digest)
    return {
        "schema_id": COMPLETE_EXECUTION_IDENTITY_SCHEMA_ID,
        "scientific_input_sha256": scientific_input_hash(scientific_core),
        "runtime_source_closure_sha256": closure_digest,
        "run_identity": {
            "experiment_id": record["experiment_id"],
            "run_id": record["run_id"],
            "execution_ordinal_zero_based": record[
                "execution_ordinal_zero_based"
            ],
            "execution_role": record["execution_role"],
            "mechanism_configuration_role": record[
                "mechanism_configuration_role"
            ],
            "paired_run_id": record["paired_run_id"],
        },
        "instrumentation_contract": {
            "enabled": record["instrumentation_enabled"],
            "read_only": record["instrumentation_read_only"],
            "observable_ids": copy.deepcopy(record["instrumented_observable_ids"]),
            "trajectory_identity_required": record[
                "trajectory_identity_required"
            ],
            "supporting_tolerance_ladder_module_enabled": record[
                "supporting_tolerance_ladder_module_enabled"
            ],
            "supporting_duration_scaling_module_enabled": record[
                "supporting_duration_scaling_module_enabled"
            ],
        },
        "output_contract": {
            "schema_version": record["output_schema_version"],
            "payload_identity_contract": record["payload_identity_contract"],
            "json_relative_output_path": record["json_relative_output_path"],
            "json_safe_filename": record["json_safe_filename"],
            "npz_relative_output_path": record["npz_relative_output_path"],
            "npz_safe_filename": record["npz_safe_filename"],
        },
        "v3_pipeline_identity": {
            "executor_id": record["executor_id"],
            "executor_sha256": record["executor_sha256"],
            "raw_evidence_assembler_id": record["raw_evidence_assembler_id"],
            "raw_evidence_assembler_sha256": record[
                "raw_evidence_assembler_sha256"
            ],
            "classifier_id": record["classifier_id"],
            "classifier_sha256": record["classifier_sha256"],
            "semantic_contract_id": record["semantic_contract_id"],
            "semantic_contract_sha256": record["semantic_contract_sha256"],
        },
        "metric_configuration_resolution": {
            "partial_template_sha256": record[
                "partial_metric_configuration_sha256"
            ],
            "role_overlay_sha256": record["role_resolution_overlay_sha256"],
            "resolved_configuration_sha256": record[
                "resolved_metric_configuration_sha256"
            ],
        },
        "historical_implementation_identity": {
            "implementation_id": record["implementation_id"],
            "implementation_sha256": record["implementation_sha256"],
        },
    }


def physical_configuration_hash(core: Mapping[str, Any]) -> str:
    if not isinstance(core, Mapping):
        raise TypeError("physical core must be a mapping")
    return sha256_bytes(canonical_json_bytes(core))


def scientific_input_hash(core: Mapping[str, Any]) -> str:
    if not isinstance(core, Mapping):
        raise TypeError("scientific core must be a mapping")
    return sha256_bytes(canonical_json_bytes(core))


def physical_configuration_core_sha256(
    record: Mapping[str, Any], closure_digest: str
) -> str:
    return physical_configuration_hash(
        build_physical_configuration_core(record, closure_digest)
    )


def scientific_input_core_sha256(
    record: Mapping[str, Any], closure_digest: str
) -> str:
    return scientific_input_hash(build_scientific_input_core(record, closure_digest))


def complete_execution_identity_sha256(
    record: Mapping[str, Any], closure_digest: str
) -> str:
    return sha256_bytes(
        canonical_json_bytes(build_complete_execution_identity_core(record, closure_digest))
    )


def full_record_identity_sha256(record: Mapping[str, Any]) -> str:
    return sha256_bytes(
        canonical_json_bytes(
            {
                "schema_id": FULL_RECORD_IDENTITY_SCHEMA_ID,
                "record": copy.deepcopy(dict(record)),
            }
        )
    )


def _matrix_records(document: Mapping[str, Any]) -> list[Mapping[str, Any]] | None:
    records = document.get("records") if isinstance(document, Mapping) else None
    if not isinstance(records, list) or any(
        not isinstance(record, Mapping) for record in records
    ):
        return None
    return records


def strict_validate_matrix(
    candidate: Mapping[str, Any], expected: Mapping[str, Any]
) -> list[str]:
    """Pure exact validator deriving the field domain from reviewed authority.

    ``expected`` may be the reviewed matrix itself or the reviewed authority
    mapping containing exact per-record and semantic hashes.  This function has
    no filesystem effects and accepts no exclusion-list hash semantics.
    """

    if not isinstance(candidate, Mapping):
        return ["RUN_MATRIX_DOCUMENT_NOT_MAPPING"]
    records = _matrix_records(candidate)
    if records is None:
        return ["RUN_MATRIX_RECORD_SCHEMA_INVALID"]
    observed_ids = tuple(str(record.get("run_id")) for record in records)
    if observed_ids != custody.EXACT_RUN_IDS:
        return ["RUN_MATRIX_ID_OR_ORDER_MISMATCH"]

    if isinstance(expected, Mapping) and "records" in expected:
        expected_records = _matrix_records(expected)
        if expected_records is None:
            return ["EXPECTED_RUN_MATRIX_RECORD_SCHEMA_INVALID"]
        expected_ids = tuple(str(record.get("run_id")) for record in expected_records)
        if expected_ids != custody.EXACT_RUN_IDS:
            return ["EXPECTED_RUN_MATRIX_ID_OR_ORDER_MISMATCH"]
        if set(candidate) != set(expected):
            return ["RUN_MATRIX_TOP_LEVEL_FIELD_SET_MISMATCH"]
        for record, expected_record in zip(records, expected_records):
            run_id = str(record["run_id"])
            if set(record) != set(expected_record):
                return [f"RUN_MATRIX_RECORD_FIELD_SET_MISMATCH:{run_id}"]
            for field in IDENTITY_DIAGNOSTIC_FIELDS:
                if canonical_json_bytes(record[field]) != canonical_json_bytes(
                    expected_record[field]
                ):
                    return [f"RUN_MATRIX_IDENTITY_FIELD_MISMATCH:{field}"]
            if canonical_json_bytes(record) != canonical_json_bytes(expected_record):
                return [f"RUN_MATRIX_RECORD_IDENTITY_MISMATCH:{run_id}"]
        if canonical_json_bytes(candidate) != canonical_json_bytes(expected):
            return ["RUN_MATRIX_DOCUMENT_IDENTITY_MISMATCH"]
        return []

    expected_hashes = expected.get("expected_full_record_sha256_by_run_id")
    expected_fields = expected.get("expected_identity_fields_by_run_id")
    expected_semantic = expected.get("expected_matrix_semantic_sha256")
    if not isinstance(expected_hashes, Mapping) or not isinstance(
        expected_fields, Mapping
    ):
        return ["EXPECTED_RUN_MATRIX_AUTHORITY_MISSING"]
    if (
        set(expected_hashes) != set(custody.EXACT_RUN_IDS)
        or set(expected_fields) != set(custody.EXACT_RUN_IDS)
    ):
        return ["EXPECTED_FULL_RECORD_IDENTITY_DOMAIN_MISMATCH"]
    for record in records:
        run_id = str(record["run_id"])
        frozen_fields = expected_fields.get(run_id)
        if not isinstance(frozen_fields, Mapping):
            return [f"EXPECTED_IDENTITY_FIELD_DOMAIN_MISMATCH:{run_id}"]
        for field in IDENTITY_DIAGNOSTIC_FIELDS:
            if field not in frozen_fields or canonical_json_bytes(
                record.get(field)
            ) != canonical_json_bytes(frozen_fields[field]):
                return [f"RUN_MATRIX_IDENTITY_FIELD_MISMATCH:{field}"]
        if full_record_identity_sha256(record) != expected_hashes.get(run_id):
            return [f"RUN_MATRIX_RECORD_IDENTITY_MISMATCH:{run_id}"]
    if sha256_bytes(canonical_json_bytes(candidate)) != expected_semantic:
        return ["RUN_MATRIX_DOCUMENT_IDENTITY_MISMATCH"]
    return []


def matrix_mutation_probe(
    candidate: Mapping[str, Any], expected: Mapping[str, Any]
) -> dict[str, Any]:
    diagnostics = strict_validate_matrix(candidate, expected)
    return {
        "accepted": not diagnostics,
        "first_diagnostic": diagnostics[0] if diagnostics else None,
        "diagnostics": diagnostics,
    }


def _repo_path(repo_root: Path, relative_path: str) -> Path:
    root = repo_root.resolve()
    path = (root / relative_path).resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise RuntimeCustodyError(f"path escapes repository: {relative_path}") from exc
    return path


def _validate_freeze_anchor(anchor: Mapping[str, Any]) -> list[str]:
    """Pure validation of the accepted review anchor's execution authority."""

    if not isinstance(anchor, Mapping):
        return ["REVIEW_ANCHOR_NOT_MAPPING"]
    if anchor.get("verdict") != custody.EXPECTED_REVIEW_VERDICT:
        return ["REVIEW_ANCHOR_NOT_ACCEPTED"]
    authority = anchor.get(custody.REVIEW_AUTHORITY_FIELD)
    if not isinstance(authority, Mapping):
        return ["RUNTIME_EXECUTION_AUTHORITY_MISSING"]
    required = {
        "schema_id",
        "executor_id",
        "execution_authorized",
        "one_execution_only",
        "automatic_retries_authorized",
        "exact_run_ids",
        "pair_run_ids",
        "artifact_bindings",
        "runtime_source_closure",
        "runtime_source_closure_sha256",
        "expected_matrix_semantic_sha256",
        "expected_full_record_sha256_by_run_id",
        "expected_identity_fields_by_run_id",
        "expected_physical_configuration_sha256_by_run_id",
        "expected_scientific_input_sha256_by_run_id",
        "expected_complete_execution_sha256_by_run_id",
        "expected_resolved_metric_configuration_sha256_by_run_id",
        "canonical_directory_tree_sha256",
        "canonical_directory_tree_sha256_domain",
        "experiment_output_root_relative_path",
        "canonical_output_root_relative_path",
    }
    if not required.issubset(authority):
        return [f"RUNTIME_AUTHORITY_FIELD_MISSING:{sorted(required-set(authority))[0]}"]
    if (
        authority["executor_id"] != EXECUTOR_ID
        or authority["execution_authorized"] is not True
        or authority["one_execution_only"] is not True
        or authority["automatic_retries_authorized"] is not False
    ):
        return ["RUNTIME_EXECUTION_AUTHORITY_SEMANTICS_MISMATCH"]
    if tuple(authority["exact_run_ids"]) != custody.EXACT_RUN_IDS:
        return ["RUNTIME_AUTHORITY_RUN_ID_DOMAIN_MISMATCH"]
    if tuple(tuple(pair) for pair in authority["pair_run_ids"]) != custody.PAIR_RUN_IDS:
        return ["RUNTIME_AUTHORITY_PAIR_DOMAIN_MISMATCH"]
    if authority["experiment_output_root_relative_path"] != custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH:
        return ["RUNTIME_AUTHORITY_OUTPUT_ROOT_MISMATCH"]
    if authority["canonical_output_root_relative_path"] != custody.CANONICAL_OUTPUT_ROOT_RELATIVE_PATH:
        return ["RUNTIME_AUTHORITY_CANONICAL_ROOT_MISMATCH"]

    bindings = authority["artifact_bindings"]
    if not isinstance(bindings, Mapping) or set(bindings) != set(custody.REQUIRED_ARTIFACT_PATHS):
        return ["RUNTIME_AUTHORITY_ARTIFACT_DOMAIN_MISMATCH"]
    for name, path in custody.REQUIRED_ARTIFACT_PATHS.items():
        binding = bindings[name]
        if not isinstance(binding, Mapping) or binding.get("relative_path") != path:
            return [f"RUNTIME_AUTHORITY_ARTIFACT_PATH_MISMATCH:{name}"]
        if not _is_hex_digest(binding.get("sha256"), 64):
            return [f"RUNTIME_AUTHORITY_ARTIFACT_IDENTITY_INVALID:{name}"]

    closure = authority["runtime_source_closure"]
    if not isinstance(closure, Mapping) or not isinstance(closure.get("modules"), list):
        return ["IMPLEMENTATION_CLOSURE_SCHEMA_INVALID"]
    closure_digest = authority["runtime_source_closure_sha256"]
    if not _is_hex_digest(closure_digest, 64):
        return ["IMPLEMENTATION_CLOSURE_DIGEST_INVALID"]
    if sha256_bytes(canonical_json_bytes(closure)) != closure_digest:
        return ["IMPLEMENTATION_CLOSURE_DIGEST_MISMATCH"]
    module_by_name = {
        binding.get("module_name"): binding
        for binding in closure["modules"]
        if isinstance(binding, Mapping)
    }
    if tuple(module_by_name) != custody.REQUIRED_MODULE_NAMES:
        return ["IMPLEMENTATION_CLOSURE_MODULE_DOMAIN_MISMATCH"]
    for module_name, relative_path in custody.MODULE_PATH_BY_NAME.items():
        binding = module_by_name[module_name]
        if binding.get("relative_path") != relative_path:
            return [f"IMPLEMENTATION_CLOSURE_MODULE_PATH_MISMATCH:{module_name}"]
        if (
            not _is_hex_digest(binding.get("sha256"), 64)
            or binding.get("loader_type") != "SourceFileLoader"
            or binding.get("expected_resolved_relative_path") != relative_path
        ):
            return [f"IMPLEMENTATION_CLOSURE_MODULE_IDENTITY_INVALID:{module_name}"]

    for field in (
        "expected_full_record_sha256_by_run_id",
        "expected_physical_configuration_sha256_by_run_id",
        "expected_scientific_input_sha256_by_run_id",
        "expected_complete_execution_sha256_by_run_id",
        "expected_resolved_metric_configuration_sha256_by_run_id",
    ):
        values = authority[field]
        if (
            not isinstance(values, Mapping)
            or set(values) != set(custody.EXACT_RUN_IDS)
        ):
            return [f"RUNTIME_AUTHORITY_HASH_DOMAIN_MISMATCH:{field}"]
        if any(not _is_hex_digest(value, 64) for value in values.values()):
            return [f"RUNTIME_AUTHORITY_HASH_VALUE_INVALID:{field}"]
    identity_fields = authority["expected_identity_fields_by_run_id"]
    if (
        not isinstance(identity_fields, Mapping)
        or set(identity_fields) != set(custody.EXACT_RUN_IDS)
    ):
        return ["RUNTIME_AUTHORITY_IDENTITY_FIELD_DOMAIN_MISMATCH"]
    if any(
        not isinstance(values, Mapping)
        or set(values) != set(IDENTITY_DIAGNOSTIC_FIELDS)
        for values in identity_fields.values()
    ):
        return ["RUNTIME_AUTHORITY_IDENTITY_FIELD_VALUE_MISMATCH"]
    if not _is_hex_digest(authority["expected_matrix_semantic_sha256"], 64):
        return ["RUNTIME_AUTHORITY_MATRIX_DIGEST_INVALID"]
    if not _is_hex_digest(authority["canonical_directory_tree_sha256"], 64):
        return ["RUNTIME_AUTHORITY_CANONICAL_DIGEST_INVALID"]
    return []


def _load_reviewed_authority(
    repo_root: str | Path,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Load only the fixed reviewed-v3 anchor; no caller path is accepted."""

    root = Path(repo_root).resolve()
    path = _repo_path(root, custody.REVIEW_ANCHOR_RELATIVE_PATH)
    if not path.is_file():
        raise RuntimeCustodyError("accepted v3 review anchor is absent")
    contents = path.read_bytes()
    try:
        anchor = json.loads(contents.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeCustodyError("accepted v3 review anchor is not valid UTF-8 JSON") from exc
    diagnostics = _validate_freeze_anchor(anchor)
    if diagnostics:
        raise RuntimeCustodyError(diagnostics[0])
    authority = copy.deepcopy(anchor[custody.REVIEW_AUTHORITY_FIELD])
    report = {
        "relative_path": custody.REVIEW_ANCHOR_RELATIVE_PATH,
        "resolved_path": str(path),
        "verdict": anchor["verdict"],
        "sha256": sha256_bytes(contents),
        "fixed_path_bytes_loaded": True,
        "runtime_execution_authority_sha256": sha256_bytes(
            canonical_json_bytes(authority)
        ),
    }
    return authority, report


def _read_bound_file(
    repo_root: Path, binding: Mapping[str, Any]
) -> tuple[bytes, dict[str, Any]]:
    relative_path = str(binding["relative_path"])
    path = _repo_path(repo_root, relative_path)
    if not path.is_file():
        raise RuntimeCustodyError(f"required bound file missing: {relative_path}")
    contents = path.read_bytes()
    actual_sha = sha256_bytes(contents)
    if actual_sha != binding["sha256"]:
        raise RuntimeCustodyError(f"bound file identity mismatch: {relative_path}")
    return contents, {
        "relative_path": relative_path,
        "resolved_path": str(path),
        "sha256": actual_sha,
        "path_exact": True,
        "bytes_exact": True,
    }


def _attest_loaded_module(
    repo_root: Path, module: ModuleType, binding: Mapping[str, Any]
) -> dict[str, Any]:
    expected_path = _repo_path(repo_root, str(binding["relative_path"]))
    spec_origin = getattr(getattr(module, "__spec__", None), "origin", None)
    if module.__name__ != binding["module_name"]:
        raise RuntimeCustodyError("loaded module name mismatch")
    if getattr(module, "__file__", None) is None or Path(module.__file__).resolve() != expected_path:
        raise RuntimeCustodyError(f"loaded module path mismatch: {module.__name__}")
    if spec_origin is None or Path(spec_origin).resolve() != expected_path:
        raise RuntimeCustodyError(f"loaded module origin mismatch: {module.__name__}")
    loader = getattr(getattr(module, "__spec__", None), "loader", None)
    if type(loader).__name__ != binding["loader_type"]:
        raise RuntimeCustodyError(f"loaded module loader mismatch: {module.__name__}")
    contents = expected_path.read_bytes()
    if sha256_bytes(contents) != binding["sha256"]:
        raise RuntimeCustodyError(f"loaded module byte identity mismatch: {module.__name__}")
    return {
        "module_name": module.__name__,
        "relative_path": binding["relative_path"],
        "resolved_loaded_path": str(expected_path),
        "module_spec_origin": str(Path(spec_origin).resolve()),
        "sha256": sha256_bytes(contents),
        "loader_type": type(loader).__name__,
        "path_exact": True,
        "bytes_exact": True,
        "loader_exact": True,
    }


def _attest_actual_loaded_modules_with_authority(
    repo_root: Path, authority: Mapping[str, Any]
) -> dict[str, Any]:
    closure = authority["runtime_source_closure"]
    reports = []
    modules: dict[str, ModuleType] = {}
    for binding in closure["modules"]:
        module = importlib.import_module(str(binding["module_name"]))
        if sys.modules.get(module.__name__) is not module:
            raise RuntimeCustodyError(f"import cache identity mismatch: {module.__name__}")
        modules[module.__name__] = module
        reports.append(_attest_loaded_module(repo_root, module, binding))
    v0 = modules[custody.V0_IMPLEMENTATION_MODULE]
    evolution = modules[custody.HISTORICAL_EVOLUTION_MODULE]
    packed = modules[custody.HISTORICAL_PACK_MODULE]
    loaded_evolution, loaded_pack = v0._load_historical_implementation()
    if loaded_evolution is not evolution or loaded_pack is not packed:
        raise RuntimeCustodyError("historical module object binding mismatch")
    if getattr(evolution, "accepted_v0", None) is not packed:
        raise RuntimeCustodyError("historical evolution-to-pack binding mismatch")
    operator = closure.get("operator_configuration")
    if not isinstance(operator, Mapping):
        raise RuntimeCustodyError("operator configuration missing from closure")
    if float(evolution.LENGTH) != float(operator.get("length")) or float(evolution.WILSON_R) != float(operator.get("wilson_r")):
        raise RuntimeCustodyError("loaded operator scalar configuration mismatch")
    return {
        "all_passed": True,
        "loaded_module_count": len(reports),
        "loaded_modules": reports,
        "runtime_source_closure_sha256": authority[
            "runtime_source_closure_sha256"
        ],
        "historical_object_binding_exact": True,
        "operator_configuration": copy.deepcopy(operator),
    }


def attest_actual_loaded_modules(repo_root: str | Path) -> dict[str, Any]:
    authority, _ = _load_reviewed_authority(repo_root)
    return _attest_actual_loaded_modules_with_authority(
        Path(repo_root).resolve(), authority
    )


def _validate_matrix_against_authority(
    matrix: Mapping[str, Any], authority: Mapping[str, Any]
) -> None:
    diagnostics = strict_validate_matrix(matrix, authority)
    if diagnostics:
        raise RuntimeCustodyError(diagnostics[0])
    records = _matrix_records(matrix)
    assert records is not None
    closure_digest = str(authority["runtime_source_closure_sha256"])
    by_id = {str(record["run_id"]): record for record in records}
    for record in records:
        run_id = str(record["run_id"])
        physical = build_physical_configuration_core(record, closure_digest)
        scientific = build_scientific_input_core(record, closure_digest)
        complete = build_complete_execution_identity_core(record, closure_digest)
        partial = record.get("partial_metric_configuration")
        overlay = record.get("role_resolution_overlay")
        if not isinstance(partial, Mapping) or not isinstance(overlay, Mapping):
            raise RuntimeCustodyError(f"metric configuration resolution missing: {run_id}")
        resolved = resolve_frozen_metric_configuration(record, partial, overlay)
        plan_record = build_read_only_execution_plan_record(
            record, resolved, overlay
        )
        physical_sha = physical_configuration_hash(physical)
        scientific_sha = scientific_input_hash(scientific)
        complete_sha = sha256_bytes(canonical_json_bytes(complete))
        partial_sha = sha256_bytes(canonical_json_bytes(partial))
        overlay_sha = sha256_bytes(canonical_json_bytes(overlay))
        resolved_sha = sha256_bytes(canonical_json_bytes(resolved))
        if record.get("physical_configuration_core") != physical:
            raise RuntimeCustodyError(f"embedded physical core mismatch: {run_id}")
        if record.get("physical_configuration_core_sha256") != physical_sha:
            raise RuntimeCustodyError(f"embedded physical core hash mismatch: {run_id}")
        if record.get("scientific_input_core") != scientific:
            raise RuntimeCustodyError(f"embedded scientific core mismatch: {run_id}")
        if record.get("scientific_input_core_sha256") != scientific_sha or record.get("input_hash") != scientific_sha:
            raise RuntimeCustodyError(f"scientific input hash mismatch: {run_id}")
        if record.get("runtime_source_closure_sha256") != closure_digest:
            raise RuntimeCustodyError(f"runtime source closure binding mismatch: {run_id}")
        if record.get("complete_execution_identity_core") != complete:
            raise RuntimeCustodyError(f"complete execution identity mismatch: {run_id}")
        if record.get("complete_execution_identity_sha256") != complete_sha:
            raise RuntimeCustodyError(f"complete execution identity hash mismatch: {run_id}")
        if record.get("partial_metric_configuration_sha256") != partial_sha:
            raise RuntimeCustodyError(f"partial metric template hash mismatch: {run_id}")
        if record.get("role_resolution_overlay_sha256") != overlay_sha:
            raise RuntimeCustodyError(f"role resolution overlay hash mismatch: {run_id}")
        if record.get("resolved_metric_configuration") != resolved:
            raise RuntimeCustodyError(f"resolved metric configuration mismatch: {run_id}")
        if record.get("resolved_metric_configuration_sha256") != resolved_sha:
            raise RuntimeCustodyError(f"resolved metric configuration hash mismatch: {run_id}")
        if plan_record.get("simulation_entered") is not False:
            raise RuntimeCustodyError(f"read-only plan entered simulation: {run_id}")
        if physical_sha != authority["expected_physical_configuration_sha256_by_run_id"][run_id]:
            raise RuntimeCustodyError(f"reviewed physical hash mismatch: {run_id}")
        if scientific_sha != authority["expected_scientific_input_sha256_by_run_id"][run_id]:
            raise RuntimeCustodyError(f"reviewed scientific hash mismatch: {run_id}")
        if complete_sha != authority["expected_complete_execution_sha256_by_run_id"][run_id]:
            raise RuntimeCustodyError(f"reviewed complete execution hash mismatch: {run_id}")
        if resolved_sha != authority[
            "expected_resolved_metric_configuration_sha256_by_run_id"
        ][run_id]:
            raise RuntimeCustodyError(f"reviewed resolved metric hash mismatch: {run_id}")
    for instrumented_id, control_id in custody.PAIR_RUN_IDS:
        if by_id[instrumented_id]["physical_configuration_core_sha256"] != by_id[control_id]["physical_configuration_core_sha256"]:
            raise RuntimeCustodyError(f"paired physical configuration mismatch: {instrumented_id}")
    scientific_hashes = [
        str(by_id[run_id]["scientific_input_core_sha256"])
        for run_id in custody.EXACT_RUN_IDS
    ]
    if len(set(scientific_hashes)) != len(custody.PAIR_RUN_IDS):
        raise RuntimeCustodyError("scientific input hashes do not form three physical pairs")
    complete_hashes = [
        str(by_id[run_id]["complete_execution_identity_sha256"])
        for run_id in custody.EXACT_RUN_IDS
    ]
    if len(set(complete_hashes)) != len(custody.EXACT_RUN_IDS):
        raise RuntimeCustodyError("complete execution identities are not six-distinct")


def _environment_report(v0: ModuleType) -> dict[str, Any]:
    if platform.python_version() != v0.EXPECTED_PYTHON_VERSION:
        raise RuntimeCustodyError("Python version mismatch")
    if np.__version__ != v0.EXPECTED_NUMPY_VERSION:
        raise RuntimeCustodyError("NumPy version mismatch")
    actual = {key: os.environ.get(key) for key in v0.REQUIRED_EXECUTION_ENVIRONMENT}
    if actual != dict(v0.REQUIRED_EXECUTION_ENVIRONMENT):
        raise RuntimeCustodyError("required process environment mismatch")
    return {
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "operating_system": platform.system(),
        "os_release": platform.release(),
        "machine": platform.machine(),
        "required_process_environment": actual,
    }


def _validate_canonical_parent_projection(
    repo_root: Path,
    future_records: Sequence[Mapping[str, Any]],
    canonical_matrix: Mapping[str, Any],
    closure_digest: str,
) -> dict[str, Any]:
    canonical_records = canonical_matrix.get("records")
    if not isinstance(canonical_records, list):
        raise RuntimeCustodyError("canonical matrix record schema invalid")
    by_id = {
        str(record["run_id"]): record
        for record in canonical_records
        if isinstance(record, Mapping) and "run_id" in record
    }
    reports = []
    for future in future_records:
        run_id = str(future["run_id"])
        parent_id = str(future["parent_canonical_run_id"])
        parent = by_id.get(parent_id)
        if parent is None:
            raise RuntimeCustodyError(f"canonical parent missing: {run_id}")
        expected_row = {"row_id": parent["scientific_row_id"], **copy.deepcopy(parent["requested_axis_values"])}
        comparisons = {
            "parent_input_hash": future["parent_canonical_input_hash"] == parent["input_hash"],
            "initial_condition_identity": future["parent_initial_condition_identity"] == parent["initial_condition_identity"],
            "scientific_row_id": future["scientific_row_id"] == parent["scientific_row_id"],
            "row": future["row"] == expected_row,
            "model": future["model_class"] == parent["model_or_comparator_class"],
            "n": future["n"] == parent["grid_size"],
            "dt": future["dt"] == parent["time_step"],
            "duration": future["duration"] == parent["duration"],
            "tolerance": future["tolerance"] == parent["solver_tolerance"],
            "max_iterations": future["max_iterations"] == parent["iteration_cap"],
        }
        if not all(comparisons.values()):
            failed = next(name for name, passed in comparisons.items() if not passed)
            raise RuntimeCustodyError(f"canonical parent projection mismatch: {run_id}:{failed}")
        parent_path = _repo_path(repo_root, str(future["parent_canonical_output_path"]))
        output_bytes = parent_path.read_bytes()
        if sha256_bytes(output_bytes) != future["parent_canonical_output_sha256"]:
            raise RuntimeCustodyError(f"canonical parent output hash mismatch: {run_id}")
        output = json.loads(output_bytes.decode("utf-8"))
        if output.get("run_id") != parent_id or output.get("input_hash") != parent["input_hash"]:
            raise RuntimeCustodyError(f"canonical parent output echo mismatch: {run_id}")
        reports.append(
            {
                "run_id": run_id,
                "parent_run_id": parent_id,
                "parent_input_hash": parent["input_hash"],
                "parent_output_sha256": sha256_bytes(output_bytes),
                "physical_configuration_core_sha256": physical_configuration_core_sha256(future, closure_digest),
                "scientific_input_core_sha256": scientific_input_core_sha256(future, closure_digest),
                "all_projection_fields_exact": True,
            }
        )
    return {"all_passed": True, "records": reports}


@dataclass(frozen=True)
class _ExecutionPlan:
    records: tuple[dict[str, Any], ...]
    resolved_metric_configurations: Mapping[str, dict[str, Any]]
    read_only_plan_records: tuple[dict[str, Any], ...]
    report: dict[str, Any]
    v0: ModuleType


def _prepare_execution_plan(repo_root: str | Path) -> _ExecutionPlan:
    root = Path(repo_root).resolve()
    authority, anchor_report = _load_reviewed_authority(root)
    artifact_bytes: dict[str, bytes] = {}
    artifact_reports = []
    matrix_binding = authority["artifact_bindings"]["run_matrix"]
    matrix_path = _repo_path(root, matrix_binding["relative_path"])
    if not matrix_path.is_file():
        raise RuntimeCustodyError("required bound run matrix missing")
    matrix_raw = matrix_path.read_bytes()
    try:
        matrix = json.loads(matrix_raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RuntimeCustodyError("run matrix is not valid UTF-8 JSON") from exc
    _validate_matrix_against_authority(matrix, authority)
    if sha256_bytes(matrix_raw) != matrix_binding["sha256"]:
        raise RuntimeCustodyError("RUN_MATRIX_DOCUMENT_IDENTITY_MISMATCH")
    artifact_bytes["run_matrix"] = matrix_raw
    artifact_reports.append(
        {
            "relative_path": matrix_binding["relative_path"],
            "resolved_path": str(matrix_path),
            "sha256": sha256_bytes(matrix_raw),
            "path_exact": True,
            "bytes_exact": True,
        }
    )
    for name in custody.REQUIRED_ARTIFACT_PATHS:
        if name == "run_matrix":
            continue
        contents, report = _read_bound_file(root, authority["artifact_bindings"][name])
        artifact_bytes[name] = contents
        artifact_reports.append(report)
    records = tuple(copy.deepcopy(matrix["records"]))
    packet = json.loads(artifact_bytes["freeze_packet"].decode("utf-8"))
    resolution_contract = packet.get("metric_configuration_resolution_contract")
    if not isinstance(resolution_contract, Mapping):
        raise RuntimeCustodyError("metric configuration resolution contract missing")
    canonical_matrix = json.loads(artifact_bytes["canonical_matrix"].decode("utf-8"))
    module_report = _attest_actual_loaded_modules_with_authority(root, authority)
    v0 = sys.modules[custody.V0_IMPLEMENTATION_MODULE]
    resolved_by_run_id: dict[str, dict[str, Any]] = {}
    read_only_plan_records: list[dict[str, Any]] = []
    for record in records:
        run_id = str(record["run_id"])
        partial = record["partial_metric_configuration"]
        overlay = record["role_resolution_overlay"]
        resolved = resolve_frozen_metric_configuration(record, partial, overlay)
        if resolved != record["resolved_metric_configuration"]:
            raise RuntimeCustodyError(
                f"runtime role resolution differs from frozen value: {run_id}"
            )
        v0._validate_metric_configuration(resolved["metric_configuration"])
        resolved_sha = sha256_bytes(canonical_json_bytes(resolved))
        if resolved_sha != authority[
            "expected_resolved_metric_configuration_sha256_by_run_id"
        ][run_id]:
            raise RuntimeCustodyError(
                f"runtime resolved metric identity mismatch: {run_id}"
            )
        resolved_by_run_id[run_id] = resolved
        read_only_plan_records.append(
            build_read_only_execution_plan_record(record, resolved, overlay)
        )
    if len(read_only_plan_records) != len(custody.EXACT_RUN_IDS):
        raise RuntimeCustodyError("read-only execution plan count mismatch")
    environment = _environment_report(v0)
    closure_digest = str(authority["runtime_source_closure_sha256"])
    parent_projection = _validate_canonical_parent_projection(root, records, canonical_matrix, closure_digest)

    output_root = _repo_path(root, custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH)
    canonical_root = _repo_path(root, custody.CANONICAL_OUTPUT_ROOT_RELATIVE_PATH)
    if output_root.exists():
        raise RuntimeCustodyError("mechanism output root already exists")
    if not canonical_root.is_dir():
        raise RuntimeCustodyError("canonical output root missing")
    canonical_digest = v0.directory_tree_sha256(canonical_root)
    if canonical_digest != authority["canonical_directory_tree_sha256"]:
        raise RuntimeCustodyError("canonical directory-tree digest mismatch")

    report = {
        "schema_id": RUNTIME_PREFLIGHT_SCHEMA_ID,
        "executor_id": EXECUTOR_ID,
        "review_anchor": anchor_report,
        "runtime_execution_authority_sha256": anchor_report[
            "runtime_execution_authority_sha256"
        ],
        "runtime_source_closure_sha256": closure_digest,
        "exact_run_ids": list(custody.EXACT_RUN_IDS),
        "pair_run_ids": [list(pair) for pair in custody.PAIR_RUN_IDS],
        "run_lookup_contract": "FIXED_REVIEWED_MATRIX; RUN_ID_ONLY_LOOKUP; NO_CALLER_RECORDS",
        "artifact_attestation": artifact_reports,
        "loaded_module_attestation": module_report,
        "matrix_file_sha256": sha256_bytes(artifact_bytes["run_matrix"]),
        "matrix_semantic_sha256": sha256_bytes(canonical_json_bytes(matrix)),
        "expected_full_record_sha256_by_run_id": copy.deepcopy(authority["expected_full_record_sha256_by_run_id"]),
        "physical_configuration_core_sha256_by_run_id": {
            str(record["run_id"]): str(record["physical_configuration_core_sha256"])
            for record in records
        },
        "scientific_input_core_sha256_by_run_id": {
            str(record["run_id"]): str(record["scientific_input_core_sha256"])
            for record in records
        },
        "complete_execution_identity_sha256_by_run_id": {
            str(record["run_id"]): str(record["complete_execution_identity_sha256"])
            for record in records
        },
        "resolved_metric_configuration_sha256_by_run_id": {
            run_id: sha256_bytes(canonical_json_bytes(resolved))
            for run_id, resolved in resolved_by_run_id.items()
        },
        "configuration_resolution_order": [
            "run_id_lookup",
            "frozen_partial_template_retrieval",
            "frozen_role_overlay_retrieval",
            "role_resolution",
            "strict_resolved_configuration_validation",
            "read_only_execution_plan_construction",
        ],
        "partial_template_direct_execution_authorized": False,
        "caller_metric_or_role_override_authorized": False,
        "read_only_execution_plan_count": len(read_only_plan_records),
        "read_only_execution_plans": read_only_plan_records,
        "simulation_entry_count": 0,
        "canonical_parent_projection": parent_projection,
        "environment": environment,
        "canonical_directory_tree_sha256": canonical_digest,
        "canonical_directory_tree_sha256_domain": authority["canonical_directory_tree_sha256_domain"],
        "output_root": str(output_root),
        "output_root_absent": True,
        "execution_invoked": False,
        "all_passed": True,
    }
    return _ExecutionPlan(
        records=records,
        resolved_metric_configurations=resolved_by_run_id,
        read_only_plan_records=tuple(read_only_plan_records),
        report=report,
        v0=v0,
    )


def preflight_frozen_execution(repo_root: str | Path) -> dict[str, Any]:
    """Read-only preflight of the fixed reviewed six-run matrix."""

    return copy.deepcopy(_prepare_execution_plan(repo_root).report)


def lookup_frozen_record(repo_root: str | Path, run_id: str) -> dict[str, Any]:
    """Strict run-ID-only lookup after complete reviewed-anchor preflight."""

    if type(run_id) is not str or run_id not in custody.EXACT_RUN_IDS:
        raise RuntimeCustodyError("run_id is not a registered frozen identity")
    plan = _prepare_execution_plan(repo_root)
    record = next(record for record in plan.records if record["run_id"] == run_id)
    return copy.deepcopy(record)


def _write_bytes_exclusive(path: Path, contents: bytes) -> None:
    if not path.parent.is_dir():
        raise RuntimeCustodyError(f"output parent missing: {path.parent}")
    with path.open("xb") as handle:
        handle.write(contents)


def execute_frozen_matrix_once_v3(repo_root: str | Path) -> dict[str, Any]:
    """Execute the internally loaded reviewed matrix exactly once.

    No caller-supplied run IDs, matrix, records, output paths, or authority are
    accepted.  Calling this remains unauthorized until the fixed accepted v3
    review anchor exists and passes every preflight check.
    """

    root = Path(repo_root).resolve()
    plan = _prepare_execution_plan(root)
    v0 = plan.v0
    output_root = _repo_path(root, custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH)
    canonical_root = _repo_path(root, custody.CANONICAL_OUTPUT_ROOT_RELATIVE_PATH)
    output_root.mkdir(exist_ok=False)
    runtime_custody = copy.deepcopy(plan.report)
    runtime_custody["execution_invoked"] = True
    _write_bytes_exclusive(
        output_root / "EXECUTION-STARTED.json",
        canonical_json_bytes(
            {
                "schema_id": EXECUTION_STARTED_SCHEMA_ID,
                "status": "EXECUTION_STARTED_NO_RETRY",
                "executor_id": EXECUTOR_ID,
                "runtime_custody": runtime_custody,
                "no_retry": True,
                "no_overwrite": True,
                "scientific_verdict_authorized_during_execution": False,
            }
        ),
    )
    payload_by_run_id: dict[str, Mapping[str, Any]] = {}
    run_custody = []
    for index, record in enumerate(plan.records):
        run_id = str(record["run_id"])
        resolved_configuration = plan.resolved_metric_configurations[run_id]
        metric_configuration = metric_configuration_for_numerical_execution(
            record,
            resolved_configuration,
            record["role_resolution_overlay"],
        )
        payload = v0.run_role_in_memory(
            record["row"],
            run_id,
            int(record["n"]),
            float(record["dt"]),
            float(record["duration"]),
            float(record["tolerance"]),
            int(record["max_iterations"]),
            instrumentation_enabled=bool(record["instrumentation_enabled"]),
            metric_configuration=metric_configuration,
        )
        payload_by_run_id[run_id] = payload
        json_target = _repo_path(root, str(record["json_relative_output_path"]))
        npz_target = _repo_path(root, str(record["npz_relative_output_path"]))
        if json_target.parent != output_root or npz_target.parent != output_root:
            raise RuntimeCustodyError("role payload path escapes experiment root")
        write_record = v0.write_run_role_payload_once(payload, json_target, npz_target)
        run_custody.append(
            {
                "run_id": run_id,
                "execution_ordinal": index + 1,
                "full_record_identity_sha256": full_record_identity_sha256(record),
                "physical_configuration_core_sha256": record["physical_configuration_core_sha256"],
                "scientific_input_core_sha256": record["scientific_input_core_sha256"],
                "complete_execution_identity_sha256": record[
                    "complete_execution_identity_sha256"
                ],
                "resolved_metric_configuration_sha256": record[
                    "resolved_metric_configuration_sha256"
                ],
                "parent_canonical_run_id": record["parent_canonical_run_id"],
                "parent_canonical_input_hash": record["parent_canonical_input_hash"],
                "parent_canonical_output_sha256": record["parent_canonical_output_sha256"],
                "physical_trajectory_sha256": payload["physical_trajectory_sha256"],
                **write_record,
            }
        )
    pair_records = []
    for instrumented_id, control_id in custody.PAIR_RUN_IDS:
        comparison = v0.compare_physical_trajectories(
            list(payload_by_run_id[instrumented_id]["physical_trajectory"]),
            list(payload_by_run_id[control_id]["physical_trajectory"]),
        )
        pair_records.append(
            {
                "instrumented_run_id": instrumented_id,
                "control_run_id": control_id,
                **comparison,
            }
        )
    canonical_after = v0.directory_tree_sha256(canonical_root)
    canonical_unchanged = canonical_after == plan.report["canonical_directory_tree_sha256"]
    all_pairs_byte_identical = all(bool(record["byte_identical"]) for record in pair_records)
    result = {
        "schema_id": MATRIX_RESULT_SCHEMA_ID,
        "status": (
            "BLOCKED_CANONICAL_OUTPUT_MUTATION"
            if not canonical_unchanged
            else "BLOCKED_INSTRUMENTATION_PERTURBATION"
            if not all_pairs_byte_identical
            else "EXECUTION_COMPLETED_ONCE"
        ),
        "executor_id": EXECUTOR_ID,
        "runtime_custody": runtime_custody,
        "exact_run_ids": list(custody.EXACT_RUN_IDS),
        "execution_count_by_run_id": {run_id: 1 for run_id in custody.EXACT_RUN_IDS},
        "run_custody": run_custody,
        "instrumentation_nonperturbation_pairs": pair_records,
        "all_pairs_byte_identical": all_pairs_byte_identical,
        "canonical_digest_before": plan.report["canonical_directory_tree_sha256"],
        "canonical_digest_after": canonical_after,
        "canonical_digest_unchanged": canonical_unchanged,
        "classifier_metrics": v0.assemble_classifier_metrics(payload_by_run_id),
        "mechanism_classification_allowed": canonical_unchanged and all_pairs_byte_identical,
        "claim_ceiling": "NUMERICAL_MECHANISM_EVIDENCE_ONLY; no robustness reclassification, materiality evaluation, physical claim, or E-REPRO",
    }
    _write_bytes_exclusive(output_root / "MATRIX-RESULT.json", canonical_json_bytes(result))
    if not canonical_unchanged:
        raise RuntimeCustodyError("canonical output digest changed during mechanism execution")
    return result


__all__ = [
    "ConfigurationResolutionError",
    "EXECUTOR_ID",
    "METRIC_BLOCK_IDS",
    "PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID",
    "RESOLVED_METRIC_CONFIGURATION_SCHEMA_ID",
    "ROLE_RESOLUTION_OVERLAY_SCHEMA_ID",
    "RuntimeCustodyError",
    "attest_actual_loaded_modules",
    "build_complete_execution_identity_core",
    "build_read_only_execution_plan_record",
    "build_physical_configuration_core",
    "build_scientific_input_core",
    "canonical_json_bytes",
    "complete_execution_identity_sha256",
    "execute_frozen_matrix_once_v3",
    "full_record_identity_sha256",
    "lookup_frozen_record",
    "matrix_mutation_probe",
    "metric_configuration_for_numerical_execution",
    "physical_configuration_core_sha256",
    "physical_configuration_hash",
    "preflight_frozen_execution",
    "resolve_frozen_metric_configuration",
    "scientific_input_core_sha256",
    "scientific_input_hash",
    "sha256_bytes",
    "strict_validate_matrix",
    "validate_partial_metric_configuration",
    "validate_resolved_metric_configuration",
    "validate_role_resolution_overlay",
]
