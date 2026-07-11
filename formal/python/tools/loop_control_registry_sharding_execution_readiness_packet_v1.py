from __future__ import annotations

import argparse
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "be985ab12d1947b188d773aaf5d9f64de097770e"
HISTORICAL_ABSENCE_COMMIT = "e2af09bbb4355604eee4566707afd3407ed6c4b9"

V0_PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v0.json"
)
V0_SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v0.json"
)
V0_PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v0.json"
)
V0_REVIEW_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)
REQUIREMENTS_REL = "requirements.ci.lock"

PACKET_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v1.json"
)
SCHEMA_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v1.json"
)
PROTOCOL_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v1.json"
)

EXPECTED_SHA256 = {
    V0_PACKET_REL: "ddca270745ebea3659cf9b53aa09c4c0c25a0983101a1d310e1f98380b3874c8",
    V0_SCHEMA_REL: "24f1f2703d9c6c2510b314d132bfdfc09ab9f6207d209bc2620eed328e176a58",
    V0_PROTOCOL_REL: "90a609f6d2be11be94b8c03ea04b1d58452a6f9b9fa26d227383fbfece195c8e",
    V0_REVIEW_REL: "7361b386c68590e776b4dcf354264c3ac07217d8dbabe56f722e8cb5c2b97982",
    REQUIREMENTS_REL: "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
}

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
PACKET_TARGET = "prepare_loop_control_registry_sharding_execution_readiness_packet_v1"
REVIEW_TARGET = "review_loop_control_registry_sharding_execution_readiness_packet_v1"

MIGRATION_CONTROL_COUNT = 52
READINESS_REGRESSION_COUNT = 8
DISTINCT_CONTROL_COUNT = 60
EFFECTIVE_PROFILE_INVOCATION_COUNT = 199
MAX_PAYLOAD_BYTES = 2_124_270
MAX_PAYLOAD_BASE64_BYTES = 2_832_360

PATH_PATTERN = (
    "^(?!/)(?!.*//)(?![.]{1,2}(?:/|$))(?!.*(?:/[.]{1,2})(?:/|$))"
    "[A-Za-z0-9_-](?:[A-Za-z0-9._-]*[A-Za-z0-9_-])?"
    "(?:/[A-Za-z0-9_-](?:[A-Za-z0-9._-]*[A-Za-z0-9_-])?)*$"
)
BASE64_PATTERN = (
    "^(?!.*[\\s])(?:[A-Za-z0-9+/]{4})*"
    "(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$"
)

READINESS_REGRESSIONS = [
    (
        "REGISTRY-READINESS-V1-RC-001",
        "cutover_profile_omits_required_ordered_closure",
        "V1-E-READINESS-PROFILE-CLOSURE",
    ),
    (
        "REGISTRY-READINESS-V1-RC-002",
        "history_payload_invalid_or_noncanonical_base64",
        "V1-E-HISTORY-PAYLOAD-BASE64",
    ),
    (
        "REGISTRY-READINESS-V1-RC-003",
        "history_payload_declared_size_hash_or_kind_disagrees",
        "V1-E-HISTORY-PAYLOAD-ENVELOPE",
    ),
    (
        "REGISTRY-READINESS-V1-RC-004",
        "history_payload_noncanonical_json_or_rebound_record_id",
        "V1-E-HISTORY-PAYLOAD-CANONICAL-IDENTITY",
    ),
    (
        "REGISTRY-READINESS-V1-RC-005",
        "prototype_path_is_posix_absolute",
        "V1-E-PATH-POSIX-ABSOLUTE",
    ),
    (
        "REGISTRY-READINESS-V1-RC-006",
        "prototype_path_is_slash_unc",
        "V1-E-PATH-SLASH-UNC",
    ),
    (
        "REGISTRY-READINESS-V1-RC-007",
        "validation_report_passes_with_nonempty_issues",
        "V1-E-VALIDATION-REPORT-INVARIANT",
    ),
    (
        "REGISTRY-READINESS-V1-RC-008",
        "harness_success_has_mismatched_hashes_or_profile_counts",
        "V1-E-HARNESS-REPORT-INVARIANT",
    ),
]

FORBIDDEN_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/scratch/loop_control_registry_v1_prototype",
]


class CorrectiveReadinessError(ValueError):
    pass


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


@lru_cache(maxsize=None)
def _git_blob(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise CorrectiveReadinessError(f"missing reviewed source: {relative}")
    return result.stdout


@lru_cache(maxsize=None)
def _path_exists_at_source_commit(relative: str) -> bool:
    result = subprocess.run(
        [
            "git",
            "ls-tree",
            "-z",
            HISTORICAL_ABSENCE_COMMIT,
            "--",
            f":(literal){relative}",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        check=True,
    )
    return bool(result.stdout)


@lru_cache(maxsize=1)
def _inputs() -> dict[str, Any]:
    for path, expected in EXPECTED_SHA256.items():
        if _sha256(_git_blob(path)) != expected:
            raise CorrectiveReadinessError(f"reviewed source drift: {path}")
    packet = json.loads(_git_blob(V0_PACKET_REL))
    schemas = json.loads(_git_blob(V0_SCHEMA_REL))
    protocol = json.loads(_git_blob(V0_PROTOCOL_REL))
    review = json.loads(_git_blob(V0_REVIEW_REL))
    if review["accepted_scope"]["packet_acceptance"] is not False:
        raise CorrectiveReadinessError("v0 rejection boundary drift")
    if review["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise CorrectiveReadinessError("scientific target drift")
    if review["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise CorrectiveReadinessError("maintenance target drift")
    if len(protocol["typed_control_harness"]["controls"]) != MIGRATION_CONTROL_COUNT:
        raise CorrectiveReadinessError("migration control count drift")
    return {"packet": packet, "protocol": protocol, "review": review, "schemas": schemas}


def _closed_object(properties: dict[str, Any]) -> dict[str, Any]:
    return {
        "additionalProperties": False,
        "properties": properties,
        "required": list(properties),
        "type": "object",
    }


def _sha_schema() -> dict[str, Any]:
    return {"pattern": "^[0-9a-f]{64}$", "type": "string"}


def _path_schema_v1() -> dict[str, Any]:
    return {"maxLength": 240, "minLength": 1, "pattern": PATH_PATTERN, "type": "string"}


def _replace_path_schemas(node: Any) -> None:
    if isinstance(node, dict):
        if (
            node.get("type") == "string"
            and isinstance(node.get("not"), dict)
            and "pattern" in node["not"]
            and "minLength" in node
        ):
            node.clear()
            node.update(_path_schema_v1())
            return
        for value in node.values():
            _replace_path_schemas(value)
    elif isinstance(node, list):
        for value in node:
            _replace_path_schemas(value)


def _issue_schema() -> dict[str, Any]:
    return _closed_object(
        {
            "artifact_path": _path_schema_v1(),
            "control_id": {
                "pattern": "^(REGISTRY-V1-NC-[0-9]{3}|REGISTRY-READINESS-V1-RC-[0-9]{3})$",
                "type": ["string", "null"],
            },
            "error_code": {"pattern": "^V1-E-[A-Z0-9-]+$", "type": "string"},
            "json_pointer": {"type": "string"},
            "message": {"minLength": 1, "type": "string"},
        }
    )


def _validation_report_schema_v1() -> dict[str, Any]:
    common = {
        "candidate_root_sha256": _sha_schema(),
        "executed_profile_closure": {
            "items": {
                "enum": [
                    "PROTOTYPE_INTEGRITY",
                    "WRITE_SAFETY",
                    "SHADOW_PARITY",
                    "CUTOVER_ELIGIBILITY",
                ],
                "type": "string",
            },
            "minItems": 1,
            "type": "array",
        },
        "profile": {
            "enum": [
                "PROTOTYPE_INTEGRITY",
                "WRITE_SAFETY",
                "SHADOW_PARITY",
                "CUTOVER_ELIGIBILITY",
            ],
            "type": "string",
        },
        "profile_control_root_sha256": _sha_schema(),
        "schema_id": {
            "const": "LOOP_CONTROL_VALIDATION_REPORT_READINESS_v1",
            "type": "string",
        },
        "trust_anchor_sha256": _sha_schema(),
    }
    passed = _closed_object(
        {
            **common,
            "issues": {"maxItems": 0, "type": "array"},
            "passed": {"const": True, "type": "boolean"},
            "status": {"const": "PASSED", "type": "string"},
        }
    )
    failed = _closed_object(
        {
            **common,
            "issues": {"items": _issue_schema(), "minItems": 1, "type": "array"},
            "passed": {"const": False, "type": "boolean"},
            "status": {"const": "FAILED", "type": "string"},
        }
    )
    return {
        "$id": "https://toe.local/schema/readiness-v1/validation-report.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "oneOf": [passed, failed],
    }


def _profile_report_schema(direct: int, effective: int) -> dict[str, Any]:
    return _closed_object(
        {
            "baseline_after_passed": {"const": True, "type": "boolean"},
            "baseline_before_passed": {"const": True, "type": "boolean"},
            "baseline_candidate_sha256": _sha_schema(),
            "direct_control_count": {"const": direct, "type": "integer"},
            "direct_controls_passed": {"const": direct, "type": "integer"},
            "effective_control_count": {"const": effective, "type": "integer"},
            "effective_control_root_sha256": _sha_schema(),
            "effective_controls_passed": {"const": effective, "type": "integer"},
        }
    )


def _harness_report_schema_v1() -> dict[str, Any]:
    profiles = _closed_object(
        {
            "CUTOVER_ELIGIBILITY": _profile_report_schema(1, 52),
            "PROTOTYPE_INTEGRITY": _profile_report_schema(47, 47),
            "SHADOW_PARITY": _profile_report_schema(2, 51),
            "WRITE_SAFETY": _profile_report_schema(2, 49),
        }
    )
    return {
        "$id": "https://toe.local/schema/readiness-v1/control-harness-report.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "base_candidate_sha256_after": _sha_schema(),
                "base_candidate_sha256_before": _sha_schema(),
                "distinct_control_count": {"const": DISTINCT_CONTROL_COUNT, "type": "integer"},
                "effective_profile_invocation_count": {
                    "const": EFFECTIVE_PROFILE_INVOCATION_COUNT,
                    "type": "integer",
                },
                "migration_control_count": {"const": MIGRATION_CONTROL_COUNT, "type": "integer"},
                "migration_controls_passed": {"const": MIGRATION_CONTROL_COUNT, "type": "integer"},
                "profile_reports": profiles,
                "readiness_regression_control_count": {
                    "const": READINESS_REGRESSION_COUNT,
                    "type": "integer",
                },
                "readiness_regressions_passed": {
                    "const": READINESS_REGRESSION_COUNT,
                    "type": "integer",
                },
                "schema_id": {
                    "const": "LOOP_CONTROL_CONTROL_HARNESS_REPORT_READINESS_v1",
                    "type": "string",
                },
                "status": {"const": "ALL_CONTROLS_PASSED", "type": "string"},
            }
        ),
    }


def _shadow_manifest_schema_v1() -> dict[str, Any]:
    return {
        "$id": "https://toe.local/schema/readiness-v1/shadow-trace-manifest.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "consumer_scan_sha256": _sha_schema(),
                "event_count": {"minimum": 1, "type": "integer"},
                "event_jsonl_sha256": _sha_schema(),
                "migration_batch_coverage_complete": {"const": True, "type": "boolean"},
                "operation_class_coverage_complete": {"const": True, "type": "boolean"},
                "required_consumer_count": {"minimum": 1, "type": "integer"},
                "required_consumers_observed": {"minimum": 1, "type": "integer"},
                "run_id": {
                    "pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$",
                    "type": "string",
                },
                "schema_id": {
                    "const": "LOOP_CONTROL_SHADOW_TRACE_MANIFEST_READINESS_v1",
                    "type": "string",
                },
                "semantic_mismatch_count": {"const": 0, "type": "integer"},
                "status": {"const": "COMPLETE_PARITY", "type": "string"},
                "unclassified_consumer_count": {"const": 0, "type": "integer"},
                "unobserved_required_consumer_count": {"const": 0, "type": "integer"},
            }
        ),
    }


@lru_cache(maxsize=1)
def build_schema_bundle() -> dict[str, Any]:
    bundle = deepcopy(_inputs()["schemas"])
    _replace_path_schemas(bundle)
    bundle["schema_id"] = "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v1"
    bundle["status"] = (
        "CORRECTIVE_V1_CLOSED_SCHEMAS_PREPARED_AFTER_V0_REJECTION_"
        "NO_PRODUCTION_INSTALLATION_OR_EXECUTION"
    )
    bundle["correction_source"] = {
        "rejected_v0_review_path": V0_REVIEW_REL,
        "rejected_v0_review_sha256": EXPECTED_SHA256[V0_REVIEW_REL],
        "source_commit": SOURCE_COMMIT,
    }
    bundle["path_contract"] = {
        "candidate_path_pattern": PATH_PATTERN,
        "lexical_prefix_check_sufficient": False,
        "realized_paths_must_resolve_strictly_within_exact_run_root": True,
        "reparse_point_or_symlink_ancestor_allowed": False,
        "reserved_windows_device_names_rejected_semantically": True,
    }
    history = bundle["schemas"]["history_shard_record"]
    history["$id"] = "https://toe.local/schema/readiness-v1/history-record.schema.json"
    payload = history["properties"]["payload_canonical_json_utf8_base64"]
    payload.update(
        {
            "maxLength": MAX_PAYLOAD_BASE64_BYTES,
            "pattern": BASE64_PATTERN,
        }
    )
    history["properties"]["payload_size_bytes"]["maximum"] = MAX_PAYLOAD_BYTES
    index = bundle["schemas"]["history_index"]
    index["$id"] = "https://toe.local/schema/readiness-v1/history-index.schema.json"
    identity = index["properties"]["record_identity_contract"]["properties"]
    identity["preimage_fields"] = {
        "const": [
            "domain",
            "record_class",
            "source_path",
            "source_git_blob",
            "logical_key",
            "original_json_pointer",
            "payload_sha256",
            "identical_occurrence_ordinal",
        ],
        "type": "array",
    }
    index["properties"]["record_identity_contract"]["required"].append(
        "preimage_fields"
    )
    bundle["schemas"]["validation_report"] = _validation_report_schema_v1()
    bundle["schemas"]["control_harness_report"] = _harness_report_schema_v1()
    bundle["schemas"]["runtime_shadow_trace_manifest"] = _shadow_manifest_schema_v1()
    for name, schema in bundle["schemas"].items():
        if name not in {
            "history_shard_record",
            "history_index",
            "validation_report",
            "control_harness_report",
            "runtime_shadow_trace_manifest",
        }:
            schema["$id"] = (
                "https://toe.local/schema/readiness-v1/"
                + name.replace("_", "-")
                + ".schema.json"
            )
    bundle["semantic_validation_boundary"] = {
        "json_schema_only_success_authorized": False,
        "success_requires": [
            "STRUCTURAL_JSON_SCHEMA",
            "STRICT_PARSER_PROFILE",
            "NAMED_SEMANTIC_VALIDATION_PROFILE",
            "EXTERNAL_TRUST_ANCHOR_COMPARISON",
        ],
    }
    return bundle


def _profile_composition(controls: list[dict[str, Any]]) -> dict[str, Any]:
    stage_order = [
        "PROTOTYPE_INTEGRITY",
        "WRITE_SAFETY",
        "SHADOW_PARITY",
        "CUTOVER_ELIGIBILITY",
    ]
    direct = {
        stage: [row["control_id"] for row in controls if row["validator_profile"] == stage]
        for stage in stage_order
    }
    expected_direct = {
        "PROTOTYPE_INTEGRITY": 47,
        "WRITE_SAFETY": 2,
        "SHADOW_PARITY": 2,
        "CUTOVER_ELIGIBILITY": 1,
    }
    if {stage: len(rows) for stage, rows in direct.items()} != expected_direct:
        raise CorrectiveReadinessError("v0 profile assignment drift")
    entries: dict[str, Any] = {}
    cumulative: list[str] = []
    for stage in stage_order:
        cumulative.extend(direct[stage])
        closure = stage_order[: stage_order.index(stage) + 1]
        entries[stage] = {
            "direct_control_count": len(direct[stage]),
            "direct_control_ids": direct[stage],
            "effective_control_count": len(cumulative),
            "effective_control_ids": list(cumulative),
            "effective_control_root_sha256": _sha256("\n".join(cumulative).encode("utf-8")),
            "ordered_closure": closure,
        }
    entries["SHADOW_PARITY"]["live_legacy_reader_requirement"] = (
        "REQUIRED_WHILE_CAPTURING_DUAL_READ_TRACE"
    )
    entries["CUTOVER_ELIGIBILITY"]["live_legacy_reader_requirement"] = (
        "FORBIDDEN_AT_CUTOVER"
    )
    entries["CUTOVER_ELIGIBILITY"]["shadow_stage_semantics"] = (
        "VERIFY_PREVIOUSLY_ACCEPTED_IMMUTABLE_SHADOW_MANIFEST_NO_LIVE_DUAL_READ"
    )
    return {
        "candidate_selectable_profile_allowed": False,
        "composition_semantics": "EXACT_ORDERED_PREFIX_CLOSURE_ALL_LISTED_STAGES_REQUIRED",
        "effective_profile_invocation_count": EFFECTIVE_PROFILE_INVOCATION_COUNT,
        "generic_profile_parameter_allowed": False,
        "named_entrypoints": entries,
        "stage_order": stage_order,
    }


@lru_cache(maxsize=1)
def build_protocol_bundle() -> dict[str, Any]:
    protocol = deepcopy(_inputs()["protocol"])
    controls = protocol["typed_control_harness"]["controls"]
    protocol["schema_id"] = (
        "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v1"
    )
    protocol["status"] = (
        "CORRECTIVE_V1_EXECUTION_PROTOCOL_PREPARED_AFTER_V0_REJECTION_NOT_EXECUTED"
    )
    protocol["validator_profile_composition"] = _profile_composition(controls)
    protocol["typed_control_harness"].pop("validator_profiles", None)
    protocol["typed_control_harness"].update(
        {
            "distinct_control_count": DISTINCT_CONTROL_COUNT,
            "effective_profile_invocation_count": EFFECTIVE_PROFILE_INVOCATION_COUNT,
            "migration_control_count": MIGRATION_CONTROL_COUNT,
            "readiness_regression_control_count": READINESS_REGRESSION_COUNT,
            "readiness_regressions": [
                {
                    "control_id": control_id,
                    "execution_status": "NOT_EXECUTED_CORRECTIVE_PREPARATION_ONLY",
                    "expected_decision": "REJECT",
                    "expected_exact_error_set": [error],
                    "mutation": mutation,
                    "permanent": True,
                    "v0_false_acceptance_regression": True,
                }
                for control_id, mutation, error in READINESS_REGRESSIONS
            ],
        }
    )
    protocol["history_payload_validation_algorithm"] = {
        "canonical_formats": {
            "ARTIFACT_CANONICAL_JSON_v1": (
                "UTF8_SORTED_KEYS_INDENT_2_ALLOW_NAN_FALSE_EXACTLY_ONE_TERMINAL_LF"
            ),
            "HISTORY_PAYLOAD_COMPACT_JSON_v1": (
                "UTF8_SORTED_KEYS_COMMA_COLON_SEPARATORS_ALLOW_NAN_FALSE_NO_WHITESPACE_NO_FINAL_LF"
            ),
        },
        "json_schema_only_success_authorized": False,
        "maximum_decoded_bytes": MAX_PAYLOAD_BYTES,
        "maximum_encoded_bytes": MAX_PAYLOAD_BASE64_BYTES,
        "mandatory_ordered_steps": [
            "STRICT_RFC4648_BASE64_DECODE_VALIDATE_TRUE_AND_EXACT_REENCODE",
            "DECODED_LENGTH_EQUALS_PAYLOAD_SIZE_BYTES",
            "DECODED_SHA256_EQUALS_PAYLOAD_SHA256",
            "STRICT_UTF8_DUPLICATE_KEY_AND_NONFINITE_JSON_PARSE",
            "COMPACT_CANONICAL_RESERIALIZATION_EQUALS_DECODED_BYTES",
            "PARSED_TOP_LEVEL_TYPE_EQUALS_PAYLOAD_KIND_BOOL_BEFORE_NUMBER",
            "LOGICAL_KEY_POINTER_SOURCE_AND_OCCURRENCE_MATCH_SOURCE_RECORD",
            "RECOMPUTE_LOOP_CONTROL_RECORD_ID_V1_PREIMAGE",
            "RECOMPUTED_LCR1_SHA256_EQUALS_RECORD_ID",
            "FULL_RECORD_ROOTS_EQUAL_EXTERNALLY_REVIEWED_ROOTS",
        ],
        "record_id_preimage_fields": [
            "domain",
            "record_class",
            "source_path",
            "source_git_blob",
            "logical_key",
            "original_json_pointer",
            "payload_sha256",
            "identical_occurrence_ordinal",
        ],
    }
    protocol["repository_path_validation_algorithm"] = {
        "candidate_path_pattern": PATH_PATTERN,
        "exact_artifact_allowlist_required": True,
        "lexical_prefix_check_sufficient": False,
        "mandatory_ordered_steps": [
            "VALIDATE_ASCII_SAFE_POSIX_SEGMENTS_AND_RUN_ID",
            "REJECT_ABSOLUTE_UNC_DRIVE_URI_DEVICE_DOT_EMPTY_WILDCARD_CONTROL_OR_RESERVED_SEGMENTS",
            "RESOLVE_REPOSITORY_ROOT_FIXED_PROTOTYPE_BASE_AND_EXACT_RUN_ROOT",
            "REJECT_SYMLINK_JUNCTION_OR_REPARSE_POINT_IN_EVERY_EXISTING_ANCESTOR",
            "RESOLVE_DEEPEST_EXISTING_TARGET_ANCESTOR",
            "REQUIRE_TARGET_STRICTLY_WITHIN_EXACT_RUN_ROOT_BY_COMMONPATH",
            "RECHECK_CONTAINMENT_IMMEDIATELY_BEFORE_AND_AFTER_WRITE",
            "ROLLBACK_ONLY_FROM_CAPTURED_RUN_ROOT_INVENTORY",
        ],
        "prototype_base_repo_relative": (
            "formal/scratch/loop_control_registry_v1_prototype"
        ),
        "run_id_pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$",
    }
    protocol["prototype_paths"] = {
        "artifact_paths_relative_to_run_root": {
            "compatibility_reconstruction": (
                "compat/LOOP_CONTROL_REGISTRY_v0.reconstructed.json"
            ),
            "consumer_source_map": (
                "consumers/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2.json"
            ),
            "control_harness_report": (
                "validation/LOOP_CONTROL_CONTROL_HARNESS_REPORT_v1.json"
            ),
            "current_projection": "projection/LOOP_CONTROL_CURRENT_v1.prototype.json",
            "custody_manifest": (
                "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1.json"
            ),
            "custody_payload": (
                "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz"
            ),
            "history_index": (
                "history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json"
            ),
            "reconstruction_result": (
                "compat/LOOP_CONTROL_LEGACY_RECONSTRUCTION_RESULT_v1.json"
            ),
            "runtime_shadow_trace": (
                "traces/LOOP_CONTROL_RUNTIME_SHADOW_TRACE_v1.jsonl"
            ),
            "runtime_shadow_trace_manifest": (
                "traces/LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v1.json"
            ),
            "validation_report": (
                "validation/LOOP_CONTROL_REGISTRY_V1_VALIDATION_REPORT.json"
            ),
        },
        "history_shard_filename_pattern": (
            "^LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$"
        ),
        "prototype_base_repo_relative": (
            "formal/scratch/loop_control_registry_v1_prototype"
        ),
        "run_id_pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$",
    }
    protocol["success_report_invariants"] = {
        "control_harness_report": [
            "BASE_CANDIDATE_SHA256_BEFORE_EQUALS_AFTER",
            "EXACT_FOUR_PROFILE_KEYS_AND_ORDERED_CLOSURES",
            "DIRECT_COUNTS_EQUAL_47_2_2_1",
            "EFFECTIVE_COUNTS_EQUAL_47_49_51_52_AND_SUM_199",
            "EACH_BASELINE_HASH_EQUALS_TOP_LEVEL_BASELINE_HASH",
            "SUCCESS_REQUIRES_52_MIGRATION_AND_8_READINESS_CONTROLS_PASS",
        ],
        "shadow_manifest": [
            "OBSERVED_PLUS_UNOBSERVED_EQUALS_REQUIRED_CONSUMER_COUNT",
            "SUCCESS_REQUIRES_ZERO_UNOBSERVED_UNCLASSIFIED_OR_SEMANTIC_MISMATCHES",
            "EVENT_COUNT_AND_SHA256_MATCH_TRACE_BYTES_AND_ALL_EVENT_RUN_IDS_MATCH",
            "OPERATION_AND_MIGRATION_BATCH_COVERAGE_COMPLETE_WITHOUT_CONSUMER_MIGRATION",
        ],
        "validation_report": [
            "PASSED_IFF_STATUS_PASSED_AND_ISSUES_EMPTY",
            "FAILED_IFF_STATUS_FAILED_AND_ISSUES_NONEMPTY",
            "EXACT_REQUIRED_PROFILE_CLOSURE_AND_CONTROL_ROOT_EXECUTED",
            "CANDIDATE_AND_EXTERNAL_TRUST_ROOTS_VERIFIED",
            "ISSUES_DETERMINISTICALLY_SORTED_AND_TUPLE_UNIQUE",
        ],
    }
    protocol["validator_engine_and_lock_contract"].update(
        {
            "direct_requirements_lock_entry_present_at_source_commit": True,
            "requirements_lock_sha256": EXPECTED_SHA256[REQUIREMENTS_REL],
            "transitive_closure_directly_pinned": True,
        }
    )
    protocol["authorization"].update(
        {
            "corrective_v1_independent_review_authorized": True,
            "prototype_artifact_creation_authorized_now": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
        }
    )
    return protocol


@lru_cache(maxsize=1)
def build_packet() -> dict[str, Any]:
    v0 = _inputs()["packet"]
    schemas = build_schema_bundle()
    protocol = build_protocol_bundle()
    return {
        "authorization": {
            "corrective_v1_independent_review_required": True,
            "maintenance_target": MAINTENANCE_TARGET,
            "packet_target_is_current_maintenance_authority": False,
            "prototype_execution_target_selected": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "review_target_recommended_not_selected": REVIEW_TARGET,
            "scientific_target": SCIENTIFIC_TARGET,
        },
        "boundary": deepcopy(v0["boundary"]),
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "corrective_scope": {
            "distinct_control_count": DISTINCT_CONTROL_COUNT,
            "effective_profile_invocation_count": EFFECTIVE_PROFILE_INVOCATION_COUNT,
            "migration_control_count_unchanged": MIGRATION_CONTROL_COUNT,
            "readiness_regression_count": READINESS_REGRESSION_COUNT,
            "schema_count": schemas["schema_count"],
        },
        "corrective_schema_bundle": {
            "path": str(SCHEMA_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sha256": _sha256(canonical_json_bytes(schemas)),
        },
        "corrective_protocol_bundle": {
            "path": str(PROTOCOL_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sha256": _sha256(canonical_json_bytes(protocol)),
        },
        "packet_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v1"
        ),
        "packet_target": PACKET_TARGET,
        "rejected_v0_custody": {
            "corrected_test_boundary_commit": "a0d44da40922d6547f02241174fa640edb3f9fa8",
            "original_preparation_commit": "bf8c12918675d77c27c0eadde009134fc572c281",
            "review_path": V0_REVIEW_REL,
            "review_sha256": EXPECTED_SHA256[V0_REVIEW_REL],
            "v0_execution_readiness_accepted": False,
            "v0_preserved_as_historical_preparation_evidence": True,
        },
        "selection_posture": {
            "corrective_v1_acceptance_would_prove_only": (
                "CORRECTED_PREPARATION_CONTRACT_SURVIVED_INDEPENDENT_ADVERSARIAL_REVIEW"
            ),
            "cutover_selectable": False,
            "migration_execution_selectable": False,
            "prototype_execution_selectable": False,
        },
        "source_commit": SOURCE_COMMIT,
        "status": (
            "CORRECTIVE_V1_EXECUTION_READINESS_PREPARATION_CONTRACT_"
            "REVIEW_REQUIRED_NO_PROTOTYPE_MIGRATION_CUTOVER_OR_AUTHORITY"
        ),
    }


def build_all() -> dict[Path, bytes]:
    schemas = canonical_json_bytes(build_schema_bundle())
    protocol = canonical_json_bytes(build_protocol_bundle())
    packet = canonical_json_bytes(build_packet())
    return {PACKET_PATH: packet, PROTOCOL_PATH: protocol, SCHEMA_PATH: schemas}


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", suffix=".tmp", delete=False
    ) as handle:
        temporary = Path(handle.name)
        handle.write(raw)
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _forbidden_paths_absent() -> None:
    for relative in FORBIDDEN_PATHS:
        if _path_exists_at_source_commit(relative):
            raise CorrectiveReadinessError(
                f"forbidden production path existed at source commit: {relative}"
            )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build or verify corrective registry-sharding readiness v1 evidence."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    _forbidden_paths_absent()
    for path, raw in build_all().items():
        if args.check:
            if not path.exists() or path.read_bytes() != raw:
                raise SystemExit(f"corrective_readiness_v1: drift {path.relative_to(REPO_ROOT)}")
            print(
                f"corrective_readiness_v1: OK {path.relative_to(REPO_ROOT).as_posix()} "
                f"sha256={_sha256(raw)}"
            )
        else:
            _atomic_write(path, raw)
            print(
                f"corrective_readiness_v1: wrote {path.relative_to(REPO_ROOT).as_posix()} "
                f"sha256={_sha256(raw)}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
