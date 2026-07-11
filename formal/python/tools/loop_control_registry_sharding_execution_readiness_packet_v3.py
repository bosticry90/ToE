from __future__ import annotations

import argparse
import base64
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
SOURCE_COMMIT = "ee287de3db44bd4fe5a1c9c9952c07be9d2e9248"

V2_PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v2.json"
)
V2_SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v2.json"
)
V2_PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v2.json"
)
V2_REVIEW_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v2.json"
)
CONSUMER_MAP_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
REQUIREMENTS_REL = "requirements.ci.lock"

PACKET_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v3.json"
)
SCHEMA_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3.json"
)
PROTOCOL_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v3.json"
)

EXPECTED_SHA256 = {
    V2_PACKET_REL: "7b266614ef80b28595bf617110a18b5853f0171d591d2f43fd2ef06759d82f76",
    V2_SCHEMA_REL: "68dc9a1a3ab9489e84dea59be3b92db1cd0fdc8bc8185338adea007998edb03f",
    V2_PROTOCOL_REL: "38f484e16d3fb87fcfe99df4cd92a66d538ff748d8abc9e78d8600955a480e22",
    V2_REVIEW_REL: "cf1e9bdc8617824f4ab2a93d9463912665a090aa5c80f2e17589436d1df98390",
    CONSUMER_MAP_REL: "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
    REQUIREMENTS_REL: "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
}

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
PACKET_TARGET = "prepare_loop_control_registry_sharding_execution_readiness_packet_v3"
REVIEW_TARGET = "review_loop_control_registry_sharding_execution_readiness_packet_v3"

REGISTRY_PATH = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
REGISTRY_GIT_BLOB = "e6c5b3773dccd92fde9c0a8d486a56f993d6b235"
MIGRATION_CONTROL_COUNT = 52
READINESS_REGRESSION_COUNT = 8
DISTINCT_CONTROL_COUNT = 60
RUN_ID_PATTERN = "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$"
HISTORY_FIXTURE_LOGICAL_KEY = "selected"
HISTORY_SHARD_DIRECTORY = "history/shards"
JSON_POINTER_PATTERN = r"^(?:|(?:/(?:[^~/]|~[01])*)+)$"
PROTOTYPE_SHARD_RELPATH_PATTERN = (
    r"^history/shards/LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$"
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


class CorrectiveReadinessV3Error(ValueError):
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
        raise CorrectiveReadinessV3Error(f"missing reviewed source: {relative}")
    return result.stdout


@lru_cache(maxsize=1)
def _inputs() -> dict[str, Any]:
    for path, expected in EXPECTED_SHA256.items():
        if _sha256(_git_blob(path)) != expected:
            raise CorrectiveReadinessV3Error(f"reviewed source drift: {path}")
    packet = json.loads(_git_blob(V2_PACKET_REL))
    schemas = json.loads(_git_blob(V2_SCHEMA_REL))
    protocol = json.loads(_git_blob(V2_PROTOCOL_REL))
    review = json.loads(_git_blob(V2_REVIEW_REL))
    consumers = json.loads(_git_blob(CONSUMER_MAP_REL))
    if review["authorization"]["corrective_v2_preparation_accepted"] is not False:
        raise CorrectiveReadinessV3Error("v2 rejection drift")
    if review["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise CorrectiveReadinessV3Error("scientific target drift")
    if review["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise CorrectiveReadinessV3Error("maintenance target drift")
    if consumers["consumer_count"] != 496:
        raise CorrectiveReadinessV3Error("consumer baseline drift")
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


def _json_pointer_schema() -> dict[str, Any]:
    return {"pattern": JSON_POINTER_PATTERN, "type": "string"}


@lru_cache(maxsize=1)
def control_error_map() -> dict[str, str]:
    harness = _inputs()["protocol"]["typed_control_harness"]
    rows = harness["controls"] + harness["readiness_regressions"]
    mapping = {
        row["control_id"]: row["expected_exact_error_set"][0] for row in rows
    }
    if len(mapping) != DISTINCT_CONTROL_COUNT:
        raise CorrectiveReadinessV3Error("control/error map is not exactly 60 rows")
    return dict(sorted(mapping.items()))


def _issue_schema_v3() -> dict[str, Any]:
    common = {
        "artifact_path": deepcopy(
            _inputs()["protocol"]["production_validator_interface"]["error_result"]
        )["properties"]["artifact_path"],
        "json_pointer": _json_pointer_schema(),
        "message": {"minLength": 1, "type": "string"},
    }
    branches = []
    for control_id, error_code in control_error_map().items():
        branches.append(
            _closed_object(
                {
                    **common,
                    "control_id": {"const": control_id, "type": "string"},
                    "error_code": {"const": error_code, "type": "string"},
                }
            )
        )
    branches.append(
        _closed_object(
            {
                **common,
                "control_id": {"const": None, "type": "null"},
                "error_code": {
                    "const": "V1-E-NONCONTROL-DIAGNOSTIC",
                    "type": "string",
                },
            }
        )
    )
    return {"oneOf": branches}


def _replace_failed_issue_schemas(validation_schema: dict[str, Any]) -> None:
    for branch in validation_schema["oneOf"]:
        issues = branch["properties"]["issues"]
        if issues.get("minItems") == 1:
            issues["items"] = _issue_schema_v3()


def _write_path_schema_v3(path_profiles: dict[str, Any]) -> dict[str, Any]:
    repo = {
        "maxLength": 240,
        "minLength": 1,
        "pattern": path_profiles["REPOSITORY_RELPATH"]["pattern"],
        "type": "string",
    }
    prototype = {
        "maxLength": 240,
        "minLength": 1,
        "pattern": path_profiles["PROTOTYPE_ARTIFACT_RELPATH"]["pattern"],
        "type": "string",
    }
    return {
        "oneOf": [
            _closed_object(
                {
                    "path": repo,
                    "path_context": {"const": "REPOSITORY_RELPATH", "type": "string"},
                }
            ),
            _closed_object(
                {
                    "path": prototype,
                    "path_context": {
                        "const": "PROTOTYPE_ARTIFACT_RELPATH",
                        "type": "string",
                    },
                }
            ),
        ]
    }


def _field_path_profile_map() -> dict[str, str]:
    return {
        "compatibility_reconstruction_result./properties/custody_payload_identity/properties/path": "PROTOTYPE_ARTIFACT_RELPATH",
        "compatibility_reconstruction_result./properties/reconstruction_identity/properties/path": "PROTOTYPE_ARTIFACT_RELPATH",
        "compatibility_reconstruction_result./properties/source_identity/properties/path": "REPOSITORY_RELPATH",
        "compatibility_reconstruction_result./properties/validator_identity/properties/path": "REPOSITORY_RELPATH",
        "consumer_source_map./properties/baseline/properties/path": "REPOSITORY_RELPATH",
        "consumer_source_map./properties/consumers/items/properties/path": "REPOSITORY_RELPATH",
        "current_projection./properties/active_blockers/items/properties/evidence_pointer": "REPOSITORY_RELPATH",
        "current_projection./properties/active_scientific_workstream/properties/original_json_pointer": "JSON_POINTER",
        "current_projection./properties/active_scientific_workstream/properties/report": "REPOSITORY_RELPATH",
        "current_projection./properties/current_artifacts/items/properties/path": "REPOSITORY_RELPATH",
        "current_projection./properties/history_index_pointer/properties/path": "PROTOTYPE_ARTIFACT_RELPATH",
        "current_projection./properties/maintenance_authority/properties/evidence/properties/path": "REPOSITORY_RELPATH",
        "current_projection./properties/source_legacy_identity/properties/path": "REPOSITORY_RELPATH",
        "history_index./properties/consumer_source_map_pointer/properties/path": "PROTOTYPE_ARTIFACT_RELPATH",
        "history_index./properties/custody_manifest_pointer/properties/path": "PROTOTYPE_ARTIFACT_RELPATH",
        "history_index./properties/shards/items/properties/path": "PROTOTYPE_SHARD_RELPATH",
        "history_index./properties/source_registry_identity/properties/path": "REPOSITORY_RELPATH",
        "history_shard_record./properties/original_json_pointer": "JSON_POINTER",
        "history_shard_record./properties/source_path": "REPOSITORY_RELPATH",
        "legacy_byte_custody_manifest./properties/contract_pointer/properties/path": "REPOSITORY_RELPATH",
        "legacy_byte_custody_manifest./properties/generation_provenance/properties/run_id": "RUN_ID",
        "legacy_byte_custody_manifest./properties/gzip_profile/properties/path": "PROTOTYPE_ARTIFACT_RELPATH",
        "legacy_byte_custody_manifest./properties/payload_identity/properties/path": "PROTOTYPE_ARTIFACT_RELPATH",
        "legacy_byte_custody_manifest./properties/source_identity/properties/path": "REPOSITORY_RELPATH",
        "runtime_shadow_trace_event./properties/consumer_path": "REPOSITORY_RELPATH",
        "runtime_shadow_trace_event./properties/fields_accessed/items": "JSON_POINTER",
        "runtime_shadow_trace_event./properties/resolved_registry_paths/properties/candidate_prototype_path": "PROTOTYPE_ARTIFACT_RELPATH",
        "runtime_shadow_trace_event./properties/resolved_registry_paths/properties/legacy_repository_path": "REPOSITORY_RELPATH",
        "runtime_shadow_trace_event./properties/run_id": "RUN_ID",
        "runtime_shadow_trace_event./properties/write_paths/items": "CONTEXT_TAGGED_REPOSITORY_OR_PROTOTYPE_RELPATH",
        "runtime_shadow_trace_manifest./properties/run_id": "RUN_ID",
        "validation_report./oneOf/*/properties/issues/items/oneOf/*/properties/artifact_path": "PROTOTYPE_ARTIFACT_RELPATH",
        "validation_report./oneOf/*/properties/issues/items/oneOf/*/properties/json_pointer": "JSON_POINTER",
    }


@lru_cache(maxsize=1)
def build_schema_bundle() -> dict[str, Any]:
    bundle = deepcopy(_inputs()["schemas"])
    schemas = bundle["schemas"]
    path_profiles = bundle["path_profiles"]
    path_profiles["CONTEXT_TAGGED_REPOSITORY_OR_PROTOTYPE_RELPATH"] = {
        "alternatives": ["REPOSITORY_RELPATH", "PROTOTYPE_ARTIFACT_RELPATH"],
        "discriminator": "path_context",
    }
    path_profiles["PROTOTYPE_SHARD_RELPATH"] = {
        "filename_profile": "SHARD_FILENAME",
        "pattern": PROTOTYPE_SHARD_RELPATH_PATTERN,
        "resolved_containment_required": True,
    }
    _replace_failed_issue_schemas(schemas["validation_report"])
    validation_branches = schemas["validation_report"]["oneOf"]
    for branch in validation_branches:
        branch["properties"]["schema_id"] = {
            "const": "LOOP_CONTROL_VALIDATION_REPORT_READINESS_v3",
            "type": "string",
        }

    current_artifact_path = schemas["consumer_source_map"]["properties"]["consumers"][
        "items"
    ]["properties"]["path"]
    schemas["current_projection"]["properties"]["active_scientific_workstream"][
        "properties"
    ]["original_json_pointer"] = _json_pointer_schema()
    schemas["current_projection"]["properties"]["current_artifacts"]["items"][
        "properties"
    ]["path"] = deepcopy(current_artifact_path)
    schemas["history_index"]["properties"]["shards"]["items"]["properties"][
        "path"
    ] = {
        "maxLength": 240,
        "minLength": 1,
        "pattern": PROTOTYPE_SHARD_RELPATH_PATTERN,
        "type": "string",
    }
    schemas["history_shard_record"]["properties"][
        "original_json_pointer"
    ] = _json_pointer_schema()
    schemas["legacy_byte_custody_manifest"]["properties"][
        "generation_provenance"
    ]["properties"]["run_id"] = {
        "pattern": RUN_ID_PATTERN,
        "type": "string",
    }

    event = schemas["runtime_shadow_trace_event"]
    props = event["properties"]
    prototype_path = schemas["current_projection"]["properties"][
        "history_index_pointer"
    ]["properties"]["path"]
    repository_path = deepcopy(current_artifact_path)
    props.pop("resolved_registry_path", None)
    props["resolved_registry_paths"] = _closed_object(
        {
            "candidate_prototype_path": deepcopy(prototype_path),
            "legacy_repository_path": repository_path,
        }
    )
    props["write_paths"] = {
        "items": _write_path_schema_v3(path_profiles),
        "type": "array",
        "uniqueItems": True,
    }
    props["run_id"] = {"pattern": RUN_ID_PATTERN, "type": "string"}
    props["fields_accessed"]["items"] = _json_pointer_schema()
    props["trace_schema_id"] = {
        "const": "LOOP_CONTROL_SHADOW_TRACE_EVENT_v3",
        "type": "string",
    }
    event["required"] = [
        "resolved_registry_paths" if name == "resolved_registry_path" else name
        for name in event["required"]
    ]
    shadow = schemas["runtime_shadow_trace_manifest"]
    shadow["properties"]["run_id"] = {"pattern": RUN_ID_PATTERN, "type": "string"}
    shadow["properties"]["schema_id"] = {
        "const": "LOOP_CONTROL_SHADOW_TRACE_MANIFEST_READINESS_v3",
        "type": "string",
    }
    schemas["control_harness_report"]["properties"]["schema_id"] = {
        "const": "LOOP_CONTROL_CONTROL_HARNESS_REPORT_READINESS_v3",
        "type": "string",
    }
    for name, schema in schemas.items():
        schema["$id"] = (
            "https://toe.local/schema/readiness-v3/"
            + name.replace("_", "-")
            + ".schema.json"
        )
    bundle["schema_id"] = (
        "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3"
    )
    bundle["status"] = (
        "CORRECTIVE_V3_CONCRETE_FIXTURE_ISSUE_MAPPING_AND_TRACE_PATH_SCHEMAS_"
        "PREPARED_NO_PRODUCTION_INSTALLATION_OR_EXECUTION"
    )
    bundle["correction_source"] = {
        "rejected_v2_review_path": V2_REVIEW_REL,
        "rejected_v2_review_sha256": EXPECTED_SHA256[V2_REVIEW_REL],
        "source_commit": SOURCE_COMMIT,
    }
    bundle["control_error_map_sha256"] = _sha256(
        compact_json_bytes(control_error_map())
    )
    field_map = _field_path_profile_map()
    undefined_profiles = sorted(set(field_map.values()) - set(path_profiles))
    if undefined_profiles:
        raise CorrectiveReadinessV3Error(
            f"undefined field semantic profiles: {undefined_profiles}"
        )
    bundle["field_path_profile_map"] = field_map
    bundle["field_path_profile_map_contract"] = {
        "coverage": (
            "EXHAUSTIVE_FOR_SCHEMA_FILESYSTEM_PATH_JSON_POINTER_RUN_ID_AND_"
            "SHARD_FILENAME_BEARING_FIELDS"
        ),
        "mapping_count": len(field_map),
        "mapping_sha256": _sha256(compact_json_bytes(field_map)),
        "undefined_profile_count": 0,
    }
    return bundle


def _profile(name: str) -> dict[str, Any]:
    return _inputs()["protocol"]["validator_profile_composition"][
        "named_entrypoints"
    ][name]


def _validation_report(profile_name: str, passed: bool) -> dict[str, Any]:
    profile = _profile(profile_name)
    report = {
        "candidate_root_sha256": "0" * 64,
        "effective_control_count": profile["effective_control_count"],
        "executed_profile_closure": profile["ordered_closure"],
        "issues": [],
        "passed": passed,
        "profile": profile_name,
        "profile_control_root_sha256": profile["effective_control_root_sha256"],
        "schema_id": "LOOP_CONTROL_VALIDATION_REPORT_READINESS_v3",
        "status": "PASSED" if passed else "FAILED",
        "trust_anchor_sha256": "1" * 64,
    }
    if not passed:
        report["issues"] = [
            {
                "artifact_path": "validation/report.json",
                "control_id": "REGISTRY-V1-NC-001",
                "error_code": control_error_map()["REGISTRY-V1-NC-001"],
                "json_pointer": "",
                "message": "positive failed-report fixture",
            }
        ]
    return report


def _history_record_source_string() -> dict[str, Any]:
    registry = json.loads(_git_blob(REGISTRY_PATH))
    if registry.get(HISTORY_FIXTURE_LOGICAL_KEY) != "no":
        raise CorrectiveReadinessV3Error("frozen history fixture source drift")
    payload_raw = compact_json_bytes(registry[HISTORY_FIXTURE_LOGICAL_KEY])
    if payload_raw != b'"no"':
        raise CorrectiveReadinessV3Error("frozen history fixture bytes drift")
    payload_sha = _sha256(payload_raw)
    original_json_pointer = f"/{HISTORY_FIXTURE_LOGICAL_KEY}"
    preimage = compact_json_bytes(
        {
            "domain": "LOOP_CONTROL_RECORD_ID_v1",
            "identical_occurrence_ordinal": 0,
            "logical_key": HISTORY_FIXTURE_LOGICAL_KEY,
            "original_json_pointer": original_json_pointer,
            "payload_sha256": payload_sha,
            "record_class": "ROOT_FIELD",
            "source_git_blob": REGISTRY_GIT_BLOB,
            "source_path": REGISTRY_PATH,
        }
    )
    return {
        "identical_occurrence_ordinal": 0,
        "logical_key": HISTORY_FIXTURE_LOGICAL_KEY,
        "original_json_pointer": original_json_pointer,
        "payload_canonical_json_utf8_base64": base64.b64encode(payload_raw).decode(
            "ascii"
        ),
        "payload_kind": "STRING",
        "payload_sha256": payload_sha,
        "payload_size_bytes": len(payload_raw),
        "record_class": "ROOT_FIELD",
        "record_id": "lcr1:" + _sha256(preimage),
        "record_version": 1,
        "schema_id": "LOOP_CONTROL_HISTORY_RECORD_v1",
        "source_git_blob": REGISTRY_GIT_BLOB,
        "source_path": REGISTRY_PATH,
    }


def build_valid_cutover_report_v3() -> dict[str, Any]:
    return _validation_report("CUTOVER_ELIGIBILITY", True)


def build_valid_failed_report_v3() -> dict[str, Any]:
    return _validation_report("PROTOTYPE_INTEGRITY", False)


def build_valid_harness_success_v3() -> dict[str, Any]:
    return _harness_success()


def build_valid_history_payload_source_string_v3() -> dict[str, Any]:
    return _history_record_source_string()


def build_valid_passed_report_v3() -> dict[str, Any]:
    return _validation_report("PROTOTYPE_INTEGRITY", True)


def _profile_report(direct: int, effective: int, root: str) -> dict[str, Any]:
    return {
        "baseline_after_passed": True,
        "baseline_before_passed": True,
        "baseline_candidate_sha256": "a" * 64,
        "direct_control_count": direct,
        "direct_controls_passed": direct,
        "effective_control_count": effective,
        "effective_control_root_sha256": root,
        "effective_controls_passed": effective,
    }


def _harness_success() -> dict[str, Any]:
    profiles = {
        name: _profile(name)
        for name in [
            "CUTOVER_ELIGIBILITY",
            "PROTOTYPE_INTEGRITY",
            "SHADOW_PARITY",
            "WRITE_SAFETY",
        ]
    }
    return {
        "base_candidate_sha256_after": "a" * 64,
        "base_candidate_sha256_before": "a" * 64,
        "distinct_control_count": 60,
        "effective_profile_invocation_count": 199,
        "migration_control_count": 52,
        "migration_controls_passed": 52,
        "profile_reports": {
            "CUTOVER_ELIGIBILITY": _profile_report(
                1, 52, profiles["CUTOVER_ELIGIBILITY"]["effective_control_root_sha256"]
            ),
            "PROTOTYPE_INTEGRITY": _profile_report(
                47, 47, profiles["PROTOTYPE_INTEGRITY"]["effective_control_root_sha256"]
            ),
            "SHADOW_PARITY": _profile_report(
                2, 51, profiles["SHADOW_PARITY"]["effective_control_root_sha256"]
            ),
            "WRITE_SAFETY": _profile_report(
                2, 49, profiles["WRITE_SAFETY"]["effective_control_root_sha256"]
            ),
        },
        "readiness_regression_control_count": 8,
        "readiness_regressions_passed": 8,
        "schema_id": "LOOP_CONTROL_CONTROL_HARNESS_REPORT_READINESS_v3",
        "status": "ALL_CONTROLS_PASSED",
    }


@lru_cache(maxsize=1)
def positive_fixture_contracts() -> dict[str, Any]:
    fixtures = {
        "VALID_CUTOVER_REPORT_v3": (
            "validation_report",
            "build_valid_cutover_report_v3",
            build_valid_cutover_report_v3(),
        ),
        "VALID_FAILED_REPORT_v3": (
            "validation_report",
            "build_valid_failed_report_v3",
            build_valid_failed_report_v3(),
        ),
        "VALID_HARNESS_SUCCESS_v3": (
            "control_harness_report",
            "build_valid_harness_success_v3",
            build_valid_harness_success_v3(),
        ),
        "VALID_HISTORY_PAYLOAD_SOURCE_STRING_v3": (
            "history_shard_record",
            "build_valid_history_payload_source_string_v3",
            build_valid_history_payload_source_string_v3(),
        ),
        "VALID_PASSED_REPORT_v3": (
            "validation_report",
            "build_valid_passed_report_v3",
            build_valid_passed_report_v3(),
        ),
    }
    output = {}
    for fixture_id, (schema_name, builder, payload) in fixtures.items():
        artifact_validator = {
            "control_harness_report": "validate_control_harness_report_contract",
            "history_shard_record": "validate_history_record_payload_contract",
            "validation_report": "validate_validation_report_contract",
        }[schema_name]
        output[fixture_id] = {
            "artifact_contract_validator_entrypoint": artifact_validator,
            "builder_args": {},
            "builder_entrypoint": builder,
            "canonical_fixture_sha256": _sha256(canonical_json_bytes(payload)),
            "embedded_fixture_only_not_a_complete_candidate": True,
            "full_profile_baseline_executed": False,
            "full_profile_baseline_must_pass_before_mutation_at_execution": True,
            "fixture_payload": payload,
            "preparation_validator_args": {"fixture_id": fixture_id},
            "preparation_validator_entrypoint": "validate_preparation_fixture_v3",
            "schema_name": schema_name,
        }
        if schema_name == "validation_report":
            output[fixture_id]["artifact_contract_validator_args"] = {
                "expected_candidate_root_sha256": payload[
                    "candidate_root_sha256"
                ],
                "expected_profile": payload["profile"],
                "expected_trust_anchor_sha256": payload[
                    "trust_anchor_sha256"
                ],
            }
            output[fixture_id]["identity_posture"] = (
                "SYNTHETIC_PREPARATION_FIXTURE_IDENTITIES_NOT_PRODUCTION_"
                "TRUST_ANCHORS"
            )
        elif schema_name == "control_harness_report":
            output[fixture_id]["artifact_contract_validator_args"] = {
                "expected_base_candidate_sha256": payload[
                    "base_candidate_sha256_before"
                ],
                "expected_profile_control_roots": {
                    name: report["effective_control_root_sha256"]
                    for name, report in payload["profile_reports"].items()
                },
            }
            output[fixture_id]["identity_posture"] = (
                "SYNTHETIC_PREPARATION_FIXTURE_CANDIDATE_IDENTITY_NOT_A_"
                "PRODUCTION_TRUST_ANCHOR"
            )
        else:
            output[fixture_id]["artifact_contract_validator_args"] = {
                "expected_payload_sha256": payload["payload_sha256"],
                "expected_record_id": payload["record_id"],
                "expected_source_git_blob": payload["source_git_blob"],
                "expected_source_path": payload["source_path"],
            }
            output[fixture_id]["identity_posture"] = (
                "FROZEN_REVIEWED_SOURCE_MEMBERSHIP_IDENTITY"
            )
        if schema_name == "history_shard_record":
            output[fixture_id]["frozen_source_membership"] = {
                "logical_key": HISTORY_FIXTURE_LOGICAL_KEY,
                "original_json_pointer": f"/{HISTORY_FIXTURE_LOGICAL_KEY}",
                "payload_canonical_json_utf8_base64": "Im5vIg==",
                "source_git_blob": REGISTRY_GIT_BLOB,
                "source_path": REGISTRY_PATH,
                "verified_by_builder_against_source_commit": SOURCE_COMMIT,
            }
    return output


def validate_preparation_fixture_v3(
    fixture_id: str, payload: dict[str, Any] | None = None
) -> bool:
    from jsonschema.validators import validator_for

    contracts = positive_fixture_contracts()
    if fixture_id not in contracts:
        raise CorrectiveReadinessV3Error(f"unknown positive fixture: {fixture_id}")
    contract = contracts[fixture_id]
    builder = globals().get(contract["builder_entrypoint"])
    if not callable(builder):
        raise CorrectiveReadinessV3Error(
            f"missing positive fixture builder: {contract['builder_entrypoint']}"
        )
    expected = builder(**contract["builder_args"])
    candidate = expected if payload is None else payload
    if candidate != expected:
        raise CorrectiveReadinessV3Error(f"positive fixture drift: {fixture_id}")
    schema = build_schema_bundle()["schemas"][contract["schema_name"]]
    validator_class = validator_for(schema)
    validator_class.check_schema(schema)
    errors = list(validator_class(schema).iter_errors(candidate))
    if errors:
        raise CorrectiveReadinessV3Error(
            f"positive fixture schema failure: {fixture_id}: {errors[0].message}"
        )
    if _sha256(canonical_json_bytes(candidate)) != contract[
        "canonical_fixture_sha256"
    ]:
        raise CorrectiveReadinessV3Error(f"positive fixture hash drift: {fixture_id}")
    if contract["schema_name"] == "history_shard_record":
        registry = json.loads(_git_blob(REGISTRY_PATH))
        source_payload = compact_json_bytes(registry[HISTORY_FIXTURE_LOGICAL_KEY])
        decoded = base64.b64decode(
            candidate["payload_canonical_json_utf8_base64"], validate=True
        )
        if decoded != source_payload or base64.b64encode(decoded).decode("ascii") != candidate[
            "payload_canonical_json_utf8_base64"
        ]:
            raise CorrectiveReadinessV3Error("history fixture source/canonical drift")
    if contract["schema_name"] == "control_harness_report" and candidate[
        "base_candidate_sha256_before"
    ] != candidate["base_candidate_sha256_after"]:
        raise CorrectiveReadinessV3Error("harness fixture baseline identity drift")
    return True


def _patch_regressions(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    updated = deepcopy(rows)
    fixtures = positive_fixture_contracts()
    by_id = {row["control_id"]: row for row in updated}
    fixture_map = {
        "REGISTRY-READINESS-V1-RC-001": "VALID_CUTOVER_REPORT_v3",
        "REGISTRY-READINESS-V1-RC-002": "VALID_HISTORY_PAYLOAD_SOURCE_STRING_v3",
        "REGISTRY-READINESS-V1-RC-003": "VALID_HISTORY_PAYLOAD_SOURCE_STRING_v3",
        "REGISTRY-READINESS-V1-RC-004": "VALID_HISTORY_PAYLOAD_SOURCE_STRING_v3",
        "REGISTRY-READINESS-V1-RC-005": "VALID_FAILED_REPORT_v3",
        "REGISTRY-READINESS-V1-RC-006": "VALID_FAILED_REPORT_v3",
        "REGISTRY-READINESS-V1-RC-007": "VALID_PASSED_REPORT_v3",
        "REGISTRY-READINESS-V1-RC-008": "VALID_HARNESS_SUCCESS_v3",
    }
    for control_id, fixture_id in fixture_map.items():
        row = by_id[control_id]
        artifact_validator = fixtures[fixture_id][
            "artifact_contract_validator_entrypoint"
        ]
        row["full_candidate_profile_assignment"] = row["validator_profile"]
        row["full_candidate_profile_entrypoint"] = {
            "CUTOVER_ELIGIBILITY": "validate_cutover_eligibility",
            "PROTOTYPE_INTEGRITY": "validate_prototype_integrity",
            "SHADOW_PARITY": "validate_shadow_parity",
            "WRITE_SAFETY": "validate_write_safety",
        }[row["validator_profile"]]
        row["full_candidate_profile_args_derivation"] = (
            "typed_control_harness.full_profile_execution_context_derivation."
            f"profile_invocations.{row['validator_profile']}"
        )
        row["positive_fixture_id"] = fixture_id
        row["positive_fixture_contract_sha256"] = fixtures[fixture_id][
            "canonical_fixture_sha256"
        ]
        row["positive_fixture_builder_entrypoint"] = fixtures[fixture_id][
            "builder_entrypoint"
        ]
        row["mutation_precondition"] = (
            f"{fixture_id}_PASSES_VALIDATE_PREPARATION_FIXTURE_V3_BEFORE_MUTATION"
        )
        row["positive_artifact_validator_args"] = deepcopy(
            fixtures[fixture_id]["artifact_contract_validator_args"]
        )
        row["positive_artifact_validator_entrypoint"] = artifact_validator
        row["production_artifact_validator_implemented_or_executed"] = False
        row["preparation_does_not_claim_full_profile_baseline_execution"] = True
        row["realized_positive_fixture_sha256_must_be_bound_at_execution"] = True
        row["validator_entrypoint"] = artifact_validator
    by_id["REGISTRY-READINESS-V1-RC-002"]["mutation_matrix"][0].update(
        {"before": "Im5vIg==", "after": "Im5vIh=="}
    )
    by_id["REGISTRY-READINESS-V1-RC-003"]["mutation_matrix"][0].update(
        {"before": 4, "after": 5}
    )
    by_id["REGISTRY-READINESS-V1-RC-004"]["mutation_matrix"][0].update(
        {"before": "Im5vIg==", "after": "ICJubyI="}
    )
    by_id["REGISTRY-READINESS-V1-RC-007"]["mutation_matrix"][0]["after"] = [
        {
            "artifact_path": "validation/report.json",
            "control_id": "REGISTRY-READINESS-V1-RC-007",
            "error_code": control_error_map()["REGISTRY-READINESS-V1-RC-007"],
            "json_pointer": "/issues",
            "message": "atomic passed-report issue invariant probe",
        }
    ]
    by_id["REGISTRY-READINESS-V1-RC-008"]["mutation_matrix"][0].update(
        {"before": "a" * 64, "after": "b" * 64}
    )
    return updated


@lru_cache(maxsize=1)
def build_protocol_bundle() -> dict[str, Any]:
    protocol = deepcopy(_inputs()["protocol"])
    protocol["schema_id"] = (
        "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v3"
    )
    protocol["status"] = (
        "CORRECTIVE_V3_CONCRETE_FIXTURE_ISSUE_MAPPING_AND_TRACE_PATH_PROTOCOL_"
        "PREPARED_NOT_EXECUTED"
    )
    interface = protocol["production_validator_interface"]
    interface["artifact_contract_validator_entrypoints"] = {
        "control_harness_report": (
            "validate_control_harness_report_contract(report, expected_base_candidate_sha256, "
            "expected_profile_control_roots) -> ValidationResult"
        ),
        "history_shard_record": (
            "validate_history_record_payload_contract(record, expected_source_path, "
            "expected_source_git_blob, expected_record_id, expected_payload_sha256) -> ValidationResult"
        ),
        "validation_report": (
            "validate_validation_report_contract(report, expected_profile, "
            "expected_candidate_root_sha256, expected_trust_anchor_sha256) -> ValidationResult"
        ),
    }
    interface["error_result"] = _issue_schema_v3()
    report = interface["report_contract"]
    report["issues"] = "DETERMINISTICALLY_SORTED_TUPLE_UNIQUE_TYPED_LIST"
    report["passed"] = (
        "TRUE_ONLY_WHEN_ISSUES_EMPTY_AND_REQUIRED_PROFILE_CLOSURE_COMPLETED"
    )
    report["issue_schema_shared_with_validation_report"] = True
    protocol["control_error_map"] = control_error_map()
    protocol["control_error_map_sha256"] = _sha256(
        compact_json_bytes(control_error_map())
    )
    protocol["typed_control_harness"]["readiness_regressions"] = (
        _patch_regressions(
            protocol["typed_control_harness"]["readiness_regressions"]
        )
    )
    protocol["typed_control_harness"]["positive_fixture_contracts"] = (
        positive_fixture_contracts()
    )
    protocol["typed_control_harness"]["positive_fixture_contract_count"] = 5
    protocol["typed_control_harness"]["positive_fixture_scope"] = (
        "EXECUTABLE_SOURCE_BOUND_ARTIFACT_CONTRACT_FIXTURES_NOT_COMPLETE_"
        "PROTOTYPE_CANDIDATES_FULL_PROFILE_BASELINES_REQUIRED_AT_EXECUTION"
    )
    protocol["typed_control_harness"]["full_profile_execution_context_derivation"] = {
        "anchors": {
            "candidate_supplied_values_allowed": False,
            "derivation": (
                "LOAD_REVIEWED_TRUST_ANCHORS_FROM_ACCEPTED_V3_REVIEW_BINDING_"
                "AND_EXTERNAL_V1_TRUST_ANCHOR_SOURCE"
            ),
            "loader_entrypoint": "load_reviewed_trust_anchors",
            "realized_anchor_sha256_must_be_bound_by_execution_packet": True,
        },
        "candidate_root": {
            "derivation": (
                "RESOLVE_FRESH_IMMUTABLE_ARTIFACT_OVERLAY_UNDER_VALIDATED_RUN_"
                "ROOT_AND_REJECT_ESCAPE"
            ),
            "realized_path_and_tree_sha256_must_be_bound_by_execution_packet": True,
        },
        "profile_invocations": {
            "CUTOVER_ELIGIBILITY": {
                "arguments": ["candidate_root", "anchors", "accepted_trace_manifest"],
                "entrypoint": "validate_cutover_eligibility",
                "trace_manifest_derivation": (
                    "LOAD_PREVIOUSLY_ACCEPTED_IMMUTABLE_SHADOW_MANIFEST_BY_"
                    "EXECUTION_PACKET_FROZEN_PATH_AND_SHA256"
                ),
            },
            "PROTOTYPE_INTEGRITY": {
                "arguments": ["candidate_root", "anchors"],
                "entrypoint": "validate_prototype_integrity",
            },
            "SHADOW_PARITY": {
                "arguments": ["candidate_root", "anchors", "runtime_trace_manifest"],
                "entrypoint": "validate_shadow_parity",
                "trace_manifest_derivation": (
                    "BUILD_FROM_CURRENT_RUN_TRACE_BYTES_AND_BIND_PATH_SHA256_"
                    "EVENT_COUNT_AND_RUN_ID"
                ),
            },
            "WRITE_SAFETY": {
                "arguments": ["candidate_root", "anchors", "writer_probe"],
                "entrypoint": "validate_write_safety",
                "writer_probe_derivation": (
                    "CREATE_FRESH_RUN_SCOPED_PROBE_THAT_RECORDS_ALL_ATTEMPTED_"
                    "REPOSITORY_AND_PROTOTYPE_WRITES"
                ),
            },
        },
        "realized_full_profile_baselines_executed": False,
        "realized_values_may_not_be_selected_by_candidate_metadata": True,
    }
    shadow = protocol["runtime_shadow_tracing_protocol"]
    shadow["required_trace_fields"] = [
        "resolved_registry_paths" if name == "resolved_registry_path" else name
        for name in shadow["required_trace_fields"]
    ]
    shadow["trace_output"] = protocol["prototype_paths"][
        "artifact_paths_relative_to_run_root"
    ]["runtime_shadow_trace"]
    shadow["trace_output_is_relative_to_validated_run_root"] = True
    shadow["path_context_contract"] = {
        "candidate_prototype_path": "PROTOTYPE_ARTIFACT_RELPATH",
        "consumer_path": "REPOSITORY_RELPATH",
        "legacy_repository_path": "REPOSITORY_RELPATH",
        "write_paths": "CONTEXT_TAGGED_REPOSITORY_OR_PROTOTYPE_RELPATH",
    }
    protocol["success_report_invariants"]["shadow_manifest"].extend(
        [
            "WRITE_ATTEMPT_FALSE_IFF_WRITE_PATHS_EMPTY",
            "RESOLVED_LEGACY_AND_CANDIDATE_PATHS_USE_DISTINCT_CONTEXTS",
        ]
    )
    field_map = _field_path_profile_map()
    protocol["field_path_profile_map"] = field_map
    protocol["field_path_profile_map_sha256"] = _sha256(
        compact_json_bytes(field_map)
    )
    protocol["prototype_paths"]["history_shard_directory_relative_to_run_root"] = (
        HISTORY_SHARD_DIRECTORY
    )
    protocol["authorization"]["corrective_v3_independent_review_authorized"] = True
    return protocol


@lru_cache(maxsize=1)
def build_packet() -> dict[str, Any]:
    schemas = build_schema_bundle()
    protocol = build_protocol_bundle()
    return {
        "authorization": {
            "corrective_v3_independent_review_required": True,
            "maintenance_target": MAINTENANCE_TARGET,
            "packet_target_is_current_maintenance_authority": False,
            "prototype_execution_target_selected": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "review_target_recommended_not_selected": REVIEW_TARGET,
            "scientific_target": SCIENTIFIC_TARGET,
        },
        "boundary": deepcopy(_inputs()["packet"]["boundary"]),
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
            "control_error_mapping_count": 60,
            "field_path_profile_mapping_count": len(_field_path_profile_map()),
            "migration_control_count_unchanged": MIGRATION_CONTROL_COUNT,
            "positive_fixture_contract_count": 5,
            "readiness_regression_atomic_case_count": 8,
            "readiness_regression_count": READINESS_REGRESSION_COUNT,
            "schema_count": schemas["schema_count"],
        },
        "packet_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v3"
        ),
        "packet_target": PACKET_TARGET,
        "rejected_v2_custody": {
            "preparation_commit": "20a57192305cc794397fdcef06f54cab30c37205",
            "review_path": V2_REVIEW_REL,
            "review_sha256": EXPECTED_SHA256[V2_REVIEW_REL],
            "v2_execution_readiness_accepted": False,
            "v2_preserved_as_historical_corrective_evidence": True,
        },
        "selection_posture": {
            "corrective_v3_acceptance_would_prove_only": (
                "CORRECTED_PREPARATION_CONTRACT_SURVIVED_INDEPENDENT_ADVERSARIAL_REVIEW"
            ),
            "cutover_selectable": False,
            "migration_execution_selectable": False,
            "prototype_execution_selectable": False,
        },
        "source_commit": SOURCE_COMMIT,
        "status": (
            "CORRECTIVE_V3_EXECUTION_READINESS_PREPARATION_CONTRACT_"
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
        if (REPO_ROOT / relative).exists():
            raise CorrectiveReadinessV3Error(f"forbidden production path exists: {relative}")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build or verify corrective registry-sharding readiness v3 evidence."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    _forbidden_paths_absent()
    for path, raw in build_all().items():
        if args.check:
            if not path.exists() or path.read_bytes() != raw:
                raise SystemExit(f"corrective_readiness_v3: drift {path.relative_to(REPO_ROOT)}")
            print(
                f"corrective_readiness_v3: OK {path.relative_to(REPO_ROOT).as_posix()} "
                f"sha256={_sha256(raw)}"
            )
        else:
            _atomic_write(path, raw)
            print(
                f"corrective_readiness_v3: wrote {path.relative_to(REPO_ROOT).as_posix()} "
                f"sha256={_sha256(raw)}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
