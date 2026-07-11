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
SOURCE_COMMIT = "5f6672b13f1bff7653cb7caa3fc5b4e80276fc2a"
HISTORICAL_ABSENCE_COMMIT = "20a57192305cc794397fdcef06f54cab30c37205"

V1_PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v1.json"
)
V1_SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v1.json"
)
V1_PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v1.json"
)
V1_REVIEW_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v1.json"
)
CONSUMER_MAP_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
REQUIREMENTS_REL = "requirements.ci.lock"

PACKET_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v2.json"
)
SCHEMA_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v2.json"
)
PROTOCOL_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v2.json"
)

EXPECTED_SHA256 = {
    V1_PACKET_REL: "ba7275826efe754c9cdc611df32fdc4ea257017d826757de0e63206299db0261",
    V1_SCHEMA_REL: "11b6f870fd57dbc2f325d3aaa9dc5d99e4c1da303e3cee3db182f6e29f020d55",
    V1_PROTOCOL_REL: "4cb61f06e95db05593a1d9918408ceaa0cbfcc503d3720c50a8c5816781c5014",
    V1_REVIEW_REL: "54621eb5c109215ce7737e25cce37d8182256a6832fe186283df49d6b8125d4f",
    CONSUMER_MAP_REL: "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
    REQUIREMENTS_REL: "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
}

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
PACKET_TARGET = "prepare_loop_control_registry_sharding_execution_readiness_packet_v2"
REVIEW_TARGET = "review_loop_control_registry_sharding_execution_readiness_packet_v2"

MIGRATION_CONTROL_COUNT = 52
READINESS_REGRESSION_COUNT = 8
DISTINCT_CONTROL_COUNT = 60

PROTOTYPE_ARTIFACT_RELPATH_PATTERN = (
    "^(?!/)(?!.*//)(?![.]{1,2}(?:/|$))(?!.*(?:/[.]{1,2})(?:/|$))"
    "[A-Za-z0-9_-](?:[A-Za-z0-9._-]*[A-Za-z0-9_-])?"
    "(?:/[A-Za-z0-9_-](?:[A-Za-z0-9._-]*[A-Za-z0-9_-])?)*$"
)
REPOSITORY_RELPATH_PATTERN = (
    "^(?!/)(?!.*//)(?![.]{1,2}(?:/|$))(?!.*(?:/[.]{1,2})(?:/|$))"
    "(?!.*[\\\\:\\x00-\\x1f*?<>|\"])(?![^/]*[. ](?:/|$))"
    "(?!.*[/][^/]*[. ](?:/|$))[^/]+(?:/[^/]+)*$"
)
RUN_ID_PATTERN = "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$"
CONTROL_ID_PATTERN = (
    "^(?:REGISTRY-V1-NC-[0-9]{3}|REGISTRY-READINESS-V1-RC-[0-9]{3})$"
)

FORBIDDEN_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/scratch/loop_control_registry_v1_prototype",
]


class CorrectiveReadinessV2Error(ValueError):
    pass


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def compact_json_bytes(payload: Any) -> bytes:
    return json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
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
        raise CorrectiveReadinessV2Error(f"missing reviewed source: {relative}")
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
            raise CorrectiveReadinessV2Error(f"reviewed source drift: {path}")
    packet = json.loads(_git_blob(V1_PACKET_REL))
    schemas = json.loads(_git_blob(V1_SCHEMA_REL))
    protocol = json.loads(_git_blob(V1_PROTOCOL_REL))
    review = json.loads(_git_blob(V1_REVIEW_REL))
    consumers = json.loads(_git_blob(CONSUMER_MAP_REL))
    if review["authorization"]["corrective_v1_preparation_accepted"] is not False:
        raise CorrectiveReadinessV2Error("v1 rejection drift")
    if review["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise CorrectiveReadinessV2Error("scientific target drift")
    if review["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise CorrectiveReadinessV2Error("maintenance target drift")
    if consumers["consumer_count"] != 496:
        raise CorrectiveReadinessV2Error("consumer baseline drift")
    return {
        "consumers": consumers,
        "packet": packet,
        "protocol": protocol,
        "review": review,
        "schemas": schemas,
    }


def _closed_object(properties: dict[str, Any]) -> dict[str, Any]:
    return {
        "additionalProperties": False,
        "properties": properties,
        "required": list(properties),
        "type": "object",
    }


def _sha_schema() -> dict[str, Any]:
    return {"pattern": "^[0-9a-f]{64}$", "type": "string"}


def _prototype_path_schema() -> dict[str, Any]:
    return {
        "maxLength": 240,
        "minLength": 1,
        "pattern": PROTOTYPE_ARTIFACT_RELPATH_PATTERN,
        "type": "string",
    }


def _repository_path_schema() -> dict[str, Any]:
    return {
        "maxLength": 240,
        "minLength": 1,
        "pattern": REPOSITORY_RELPATH_PATTERN,
        "type": "string",
    }


def _replace_v1_paths_with_repository_paths(node: Any, v1_pattern: str) -> None:
    if isinstance(node, dict):
        if node.get("type") == "string" and node.get("pattern") == v1_pattern:
            node.clear()
            node.update(_repository_path_schema())
            return
        for value in node.values():
            _replace_v1_paths_with_repository_paths(value, v1_pattern)
    elif isinstance(node, list):
        for value in node:
            _replace_v1_paths_with_repository_paths(value, v1_pattern)


def _issue_schema_v2() -> dict[str, Any]:
    return _closed_object(
        {
            "artifact_path": _prototype_path_schema(),
            "control_id": {"pattern": CONTROL_ID_PATTERN, "type": ["string", "null"]},
            "error_code": {"pattern": "^V1-E-[A-Z0-9-]+$", "type": "string"},
            "json_pointer": {"type": "string"},
            "message": {"minLength": 1, "type": "string"},
        }
    )


def _profile_contracts(protocol: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return protocol["validator_profile_composition"]["named_entrypoints"]


def _validation_report_schema_v2(protocol: dict[str, Any]) -> dict[str, Any]:
    profiles = _profile_contracts(protocol)
    branches: list[dict[str, Any]] = []
    for profile_name in [
        "PROTOTYPE_INTEGRITY",
        "WRITE_SAFETY",
        "SHADOW_PARITY",
        "CUTOVER_ELIGIBILITY",
    ]:
        profile = profiles[profile_name]
        common = {
            "candidate_root_sha256": _sha_schema(),
            "effective_control_count": {
                "const": profile["effective_control_count"],
                "type": "integer",
            },
            "executed_profile_closure": {
                "const": profile["ordered_closure"],
                "type": "array",
            },
            "profile": {"const": profile_name, "type": "string"},
            "profile_control_root_sha256": {
                "const": profile["effective_control_root_sha256"],
                "type": "string",
            },
            "schema_id": {
                "const": "LOOP_CONTROL_VALIDATION_REPORT_READINESS_v2",
                "type": "string",
            },
            "trust_anchor_sha256": _sha_schema(),
        }
        branches.append(
            _closed_object(
                {
                    **common,
                    "issues": {"maxItems": 0, "type": "array"},
                    "passed": {"const": True, "type": "boolean"},
                    "status": {"const": "PASSED", "type": "string"},
                }
            )
        )
        branches.append(
            _closed_object(
                {
                    **common,
                    "issues": {
                        "items": _issue_schema_v2(),
                        "minItems": 1,
                        "type": "array",
                    },
                    "passed": {"const": False, "type": "boolean"},
                    "status": {"const": "FAILED", "type": "string"},
                }
            )
        )
    return {
        "$id": "https://toe.local/schema/readiness-v2/validation-report.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "oneOf": branches,
    }


def _set_prototype_path_fields(schemas: dict[str, Any]) -> None:
    current = schemas["current_projection"]["properties"]
    current["history_index_pointer"]["properties"]["path"] = _prototype_path_schema()
    current["current_artifacts"]["items"]["properties"]["path"] = _prototype_path_schema()

    index = schemas["history_index"]["properties"]
    index["consumer_source_map_pointer"]["properties"]["path"] = _prototype_path_schema()
    index["custody_manifest_pointer"]["properties"]["path"] = _prototype_path_schema()
    index["shards"]["items"]["properties"]["path"] = _prototype_path_schema()

    custody = schemas["legacy_byte_custody_manifest"]["properties"]
    custody["gzip_profile"]["properties"]["path"] = _prototype_path_schema()
    custody["payload_identity"]["properties"]["path"] = _prototype_path_schema()

    reconstruction = schemas["compatibility_reconstruction_result"]["properties"]
    reconstruction["custody_payload_identity"]["properties"]["path"] = (
        _prototype_path_schema()
    )
    reconstruction["reconstruction_identity"]["properties"]["path"] = (
        _prototype_path_schema()
    )

    event = schemas["runtime_shadow_trace_event"]["properties"]
    event["resolved_registry_path"] = _prototype_path_schema()
    event["write_paths"]["items"] = _prototype_path_schema()


@lru_cache(maxsize=1)
def build_schema_bundle() -> dict[str, Any]:
    bundle = deepcopy(_inputs()["schemas"])
    protocol = _inputs()["protocol"]
    v1_pattern = bundle["path_contract"]["candidate_path_pattern"]
    _replace_v1_paths_with_repository_paths(bundle, v1_pattern)
    schemas = bundle["schemas"]
    _set_prototype_path_fields(schemas)
    schemas["validation_report"] = _validation_report_schema_v2(protocol)
    shadow = schemas["runtime_shadow_trace_manifest"]["properties"]
    shadow["consumer_migration_performed"] = {"const": False, "type": "boolean"}
    shadow["cutover_performed"] = {"const": False, "type": "boolean"}
    schemas["runtime_shadow_trace_manifest"]["required"].extend(
        ["consumer_migration_performed", "cutover_performed"]
    )
    for name, schema in schemas.items():
        schema["$id"] = (
            "https://toe.local/schema/readiness-v2/"
            + name.replace("_", "-")
            + ".schema.json"
        )
    bundle["schema_id"] = (
        "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v2"
    )
    bundle["status"] = (
        "CORRECTIVE_V2_FIELD_TYPED_PATH_AND_RESULT_SCHEMAS_PREPARED_"
        "NO_PRODUCTION_INSTALLATION_OR_EXECUTION"
    )
    bundle["correction_source"] = {
        "rejected_v1_review_path": V1_REVIEW_REL,
        "rejected_v1_review_sha256": EXPECTED_SHA256[V1_REVIEW_REL],
        "source_commit": SOURCE_COMMIT,
    }
    bundle["path_profiles"] = {
        "JSON_POINTER": "RFC6901_VALIDATED_SEPARATELY_NOT_A_FILESYSTEM_PATH",
        "PROTOTYPE_ARTIFACT_RELPATH": {
            "pattern": PROTOTYPE_ARTIFACT_RELPATH_PATTERN,
            "resolved_containment_required": True,
        },
        "REPOSITORY_RELPATH": {
            "all_frozen_consumer_paths_must_validate": 496,
            "pattern": REPOSITORY_RELPATH_PATTERN,
        },
        "RUN_ID": {"pattern": RUN_ID_PATTERN},
        "SHARD_FILENAME": {"pattern": "^LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$"},
    }
    bundle.pop("path_contract", None)
    consumer_path_schema = schemas["consumer_source_map"]["properties"]["consumers"][
        "items"
    ]["properties"]["path"]
    import re

    incompatible = [
        row["path"]
        for row in _inputs()["consumers"]["consumers"]
        if re.fullmatch(consumer_path_schema["pattern"], row["path"]) is None
    ]
    if incompatible:
        raise CorrectiveReadinessV2Error(
            f"repository path profile rejects frozen consumers: {incompatible}"
        )
    return bundle


def _fixture_contract_hash(fixture_id: str, profile: str) -> str:
    return _sha256(
        canonical_json_bytes(
            {
                "fixture_id": fixture_id,
                "profile": profile,
                "status": "POSITIVE_BASELINE_MUST_PASS_BEFORE_MUTATION",
            }
        )
    )


def _regression_controls() -> list[dict[str, Any]]:
    specs = [
        (
            "REGISTRY-READINESS-V1-RC-001",
            "V1-E-READINESS-PROFILE-CLOSURE",
            "VALID_CUTOVER_REPORT_v2",
            "CUTOVER_ELIGIBILITY",
            "VALIDATION_REPORT",
            "mutate_cutover_closure_to_direct_only",
            "/executed_profile_closure",
            [
                "PROTOTYPE_INTEGRITY",
                "WRITE_SAFETY",
                "SHADOW_PARITY",
                "CUTOVER_ELIGIBILITY",
            ],
            ["CUTOVER_ELIGIBILITY"],
            [],
            "PROFILE_CLOSURE",
        ),
        (
            "REGISTRY-READINESS-V1-RC-002",
            "V1-E-HISTORY-PAYLOAD-BASE64",
            "VALID_HISTORY_PAYLOAD_F_v2",
            "PROTOTYPE_INTEGRITY",
            "HISTORY_RECORD",
            "mutate_base64_to_noncanonical_pad_bits",
            "/payload_canonical_json_utf8_base64",
            "Zg==",
            "Zh==",
            [],
            "PAYLOAD_BASE64",
        ),
        (
            "REGISTRY-READINESS-V1-RC-003",
            "V1-E-HISTORY-PAYLOAD-ENVELOPE",
            "VALID_HISTORY_PAYLOAD_NULL_v2",
            "PROTOTYPE_INTEGRITY",
            "HISTORY_RECORD",
            "mutate_payload_size_only",
            "/payload_size_bytes",
            4,
            5,
            [],
            "PAYLOAD_ENVELOPE",
        ),
        (
            "REGISTRY-READINESS-V1-RC-004",
            "V1-E-HISTORY-PAYLOAD-CANONICAL-IDENTITY",
            "VALID_HISTORY_PAYLOAD_NULL_v2",
            "PROTOTYPE_INTEGRITY",
            "HISTORY_RECORD",
            "mutate_payload_to_whitespace_json_and_rebind_internal_identity",
            "/payload_canonical_json_utf8_base64",
            "bnVsbA==",
            "IG51bGw=",
            [
                "payload_size_bytes",
                "payload_sha256",
                "record_id",
                "candidate_internal_record_roots",
            ],
            "PAYLOAD_CANONICAL_IDENTITY",
        ),
        (
            "REGISTRY-READINESS-V1-RC-005",
            "V1-E-PATH-POSIX-ABSOLUTE",
            "VALID_FAILED_REPORT_v2",
            "PROTOTYPE_INTEGRITY",
            "VALIDATION_ISSUE",
            "mutate_issue_path_to_posix_absolute",
            "/issues/0/artifact_path",
            "validation/report.json",
            "/absolute/report.json",
            [],
            "PROTOTYPE_PATH",
        ),
        (
            "REGISTRY-READINESS-V1-RC-006",
            "V1-E-PATH-SLASH-UNC",
            "VALID_FAILED_REPORT_v2",
            "PROTOTYPE_INTEGRITY",
            "VALIDATION_ISSUE",
            "mutate_issue_path_to_slash_unc",
            "/issues/0/artifact_path",
            "validation/report.json",
            "//server/share/report.json",
            [],
            "PROTOTYPE_PATH",
        ),
        (
            "REGISTRY-READINESS-V1-RC-007",
            "V1-E-VALIDATION-REPORT-INVARIANT",
            "VALID_PASSED_REPORT_v2",
            "PROTOTYPE_INTEGRITY",
            "VALIDATION_REPORT",
            "mutate_passed_report_add_one_issue_only",
            "/issues",
            [],
            ["ONE_VALID_ISSUE"],
            [],
            "REPORT_INVARIANT",
        ),
        (
            "REGISTRY-READINESS-V1-RC-008",
            "V1-E-HARNESS-REPORT-INVARIANT",
            "VALID_HARNESS_SUCCESS_v2",
            "PROTOTYPE_INTEGRITY",
            "HARNESS_REPORT",
            "mutate_after_candidate_hash_only",
            "/base_candidate_sha256_after",
            "BASELINE_SHA256",
            "DIFFERENT_SHA256",
            [],
            "REPORT_INVARIANT",
        ),
    ]
    rows = []
    phase_precedence = {
        "PROTOTYPE_PATH": 1,
        "PAYLOAD_BASE64": 2,
        "PAYLOAD_ENVELOPE": 3,
        "PAYLOAD_CANONICAL_IDENTITY": 4,
        "PROFILE_CLOSURE": 5,
        "REPORT_INVARIANT": 6,
    }
    for sequence, spec in enumerate(specs, start=1):
        (
            control_id,
            error,
            fixture,
            profile,
            artifact,
            mutator,
            pointer,
            before,
            after,
            rebound,
            phase,
        ) = spec
        rows.append(
            {
                "artifact_kind": artifact,
                "baseline_candidate_recreated_before_mutation": True,
                "control_id": control_id,
                "control_sequence": sequence,
                "error_phase": phase,
                "error_precedence_rank": phase_precedence[phase],
                "execution_status": "NOT_EXECUTED_CORRECTIVE_PREPARATION_ONLY",
                "expected_decision": "REJECT",
                "expected_exact_error_set": [error],
                "fixture_isolation": "FRESH_IMMUTABLE_ARTIFACT_OVERLAY",
                "mutation_matrix": [
                    {
                        "after": after,
                        "before": before,
                        "case_id": f"{control_id}-CASE-001",
                        "json_pointer": pointer,
                        "rebind_fields": rebound,
                    }
                ],
                "mutation_precondition": f"{fixture}_PASSES_{profile}",
                "mutator_entrypoint": f"{mutator}(overlay: ArtifactOverlay) -> None",
                "permanent": True,
                "positive_fixture_contract_sha256": _fixture_contract_hash(
                    fixture, profile
                ),
                "positive_fixture_id": fixture,
                "realized_positive_fixture_sha256_must_be_bound_at_execution": True,
                "rebind_candidate_internal_hashes": bool(rebound),
                "requires_runtime_trace": False,
                "requires_write_sandbox": False,
                "subsequent_controls_receive_unmodified_baseline": True,
                "v0_false_acceptance_regression": True,
                "validator_entrypoint": f"validate_{profile.lower()}",
                "validator_profile": profile,
            }
        )
    return rows


@lru_cache(maxsize=1)
def build_protocol_bundle() -> dict[str, Any]:
    protocol = deepcopy(_inputs()["protocol"])
    protocol["schema_id"] = (
        "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v2"
    )
    protocol["status"] = (
        "CORRECTIVE_V2_INTERFACE_PATH_IDENTITY_AND_ATOMIC_CONTROL_PROTOCOL_"
        "PREPARED_NOT_EXECUTED"
    )
    interface = protocol["production_validator_interface"]
    interface["error_result"] = _issue_schema_v2()
    report = interface["report_contract"]
    report.pop("errors", None)
    report["issues"] = "DETERMINISTICALLY_SORTED_TUPLE_UNIQUE_TYPED_LIST"
    report["issue_schema_shared_with_validation_report"] = True
    protocol["path_type_contract"] = {
        "JSON_POINTER": "RFC6901_NOT_A_FILESYSTEM_PATH",
        "PROTOTYPE_ARTIFACT_RELPATH": {
            "pattern": PROTOTYPE_ARTIFACT_RELPATH_PATTERN,
            "runtime_containment_required": True,
        },
        "REPOSITORY_RELPATH": {
            "frozen_consumer_compatibility_count": 496,
            "pattern": REPOSITORY_RELPATH_PATTERN,
        },
        "RUN_ID": {"pattern": RUN_ID_PATTERN},
        "SHARD_FILENAME": {"pattern": "^LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$"},
    }
    protocol["repository_path_validation_algorithm"]["candidate_path_pattern"] = (
        PROTOTYPE_ARTIFACT_RELPATH_PATTERN
    )
    payload = protocol["history_payload_validation_algorithm"]
    payload.update(
        {
            "full_record_identity_root_algorithm": (
                "SORT_RECORD_IDS_LEXICOGRAPHIC_JOIN_UTF8_LF_NO_TERMINAL_LF_SHA256"
            ),
            "identity_payload_pointer_root_algorithm": (
                "FORMAT_RECORD_ID_COLON_PAYLOAD_SHA256_COLON_POINTER_"
                "SORT_LEXICOGRAPHIC_JOIN_UTF8_LF_NO_TERMINAL_LF_SHA256"
            ),
            "original_pointer_root_algorithm": (
                "SORT_POINTERS_LEXICOGRAPHIC_JOIN_UTF8_LF_NO_TERMINAL_LF_SHA256"
            ),
            "record_id_domain_value": "LOOP_CONTROL_RECORD_ID_v1",
            "record_id_preimage_serializer": (
                "HISTORY_PAYLOAD_COMPACT_JSON_v1_UTF8_NO_TERMINAL_LF"
            ),
            "record_id_result": "lcr1:PLUS_LOWERCASE_SHA256_HEX_OF_PREIMAGE_BYTES",
        }
    )
    harness = protocol["typed_control_harness"]
    harness["readiness_regressions"] = _regression_controls()
    harness["readiness_regression_atomic_case_count"] = 8
    harness["readiness_error_aggregation"] = {
        "case_is_single_atomic_transformation": True,
        "control_passes_only_if_every_matrix_case_returns_exact_singleton_error": True,
        "error_precedence": [
            "PROTOTYPE_PATH",
            "PAYLOAD_BASE64",
            "PAYLOAD_ENVELOPE",
            "PAYLOAD_CANONICAL_IDENTITY",
            "PROFILE_CLOSURE",
            "REPORT_INVARIANT",
        ],
        "multiple_errors_for_one_atomic_case_allowed": False,
    }
    harness["constituent_semantic_tests_required"] = [
        "PAYLOAD_HASH_MISMATCH",
        "PAYLOAD_KIND_MISMATCH",
        "PAYLOAD_NONCANONICAL_BYTES",
        "FORGED_RECORD_ID",
        "VALIDATION_FAILURE_WITHOUT_ISSUE",
        "HARNESS_PROFILE_COUNT_MISMATCH",
        "SHADOW_EVENT_COUNT_OR_HASH_MISMATCH",
        "WRITE_ATTEMPT_WITH_EMPTY_WRITE_PATHS",
    ]
    protocol["success_report_invariants"]["shadow_manifest"].extend(
        [
            "CONSUMER_MIGRATION_PERFORMED_FALSE",
            "CUTOVER_PERFORMED_FALSE",
            "EVERY_EVENT_RUN_ID_EQUALS_MANIFEST_RUN_ID",
        ]
    )
    protocol["authorization"]["corrective_v2_independent_review_authorized"] = True
    return protocol


@lru_cache(maxsize=1)
def build_packet() -> dict[str, Any]:
    schemas = build_schema_bundle()
    protocol = build_protocol_bundle()
    v1_boundary = _inputs()["packet"]["boundary"]
    return {
        "authorization": {
            "corrective_v2_independent_review_required": True,
            "maintenance_target": MAINTENANCE_TARGET,
            "packet_target_is_current_maintenance_authority": False,
            "prototype_execution_target_selected": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "review_target_recommended_not_selected": REVIEW_TARGET,
            "scientific_target": SCIENTIFIC_TARGET,
        },
        "boundary": deepcopy(v1_boundary),
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "corrective_protocol_bundle": {
            "path": str(PROTOCOL_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sha256": _sha256(canonical_json_bytes(protocol)),
        },
        "corrective_schema_bundle": {
            "path": str(SCHEMA_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sha256": _sha256(canonical_json_bytes(schemas)),
        },
        "corrective_scope": {
            "distinct_path_type_count": 5,
            "migration_control_count_unchanged": MIGRATION_CONTROL_COUNT,
            "readiness_regression_atomic_case_count": 8,
            "readiness_regression_count": READINESS_REGRESSION_COUNT,
            "schema_count": schemas["schema_count"],
        },
        "packet_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v2"
        ),
        "packet_target": PACKET_TARGET,
        "rejected_v1_custody": {
            "preparation_commit": "e2af09bbb4355604eee4566707afd3407ed6c4b9",
            "review_path": V1_REVIEW_REL,
            "review_sha256": EXPECTED_SHA256[V1_REVIEW_REL],
            "v1_execution_readiness_accepted": False,
            "v1_preserved_as_historical_corrective_evidence": True,
        },
        "selection_posture": {
            "corrective_v2_acceptance_would_prove_only": (
                "CORRECTED_PREPARATION_CONTRACT_SURVIVED_INDEPENDENT_ADVERSARIAL_REVIEW"
            ),
            "cutover_selectable": False,
            "migration_execution_selectable": False,
            "prototype_execution_selectable": False,
        },
        "source_commit": SOURCE_COMMIT,
        "status": (
            "CORRECTIVE_V2_EXECUTION_READINESS_PREPARATION_CONTRACT_"
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
            raise CorrectiveReadinessV2Error(
                f"forbidden production path existed at source commit: {relative}"
            )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build or verify corrective registry-sharding readiness v2 evidence."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    _forbidden_paths_absent()
    for path, raw in build_all().items():
        if args.check:
            if not path.exists() or path.read_bytes() != raw:
                raise SystemExit(f"corrective_readiness_v2: drift {path.relative_to(REPO_ROOT)}")
            print(
                f"corrective_readiness_v2: OK {path.relative_to(REPO_ROOT).as_posix()} "
                f"sha256={_sha256(raw)}"
            )
        else:
            _atomic_write(path, raw)
            print(
                f"corrective_readiness_v2: wrote {path.relative_to(REPO_ROOT).as_posix()} "
                f"sha256={_sha256(raw)}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
