from __future__ import annotations

import argparse
import hashlib
import json
from functools import lru_cache
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "6aba59d8d399b331db010f1f5f857075b9100b7f"

PACKET_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v0.json"
)
SCHEMA_BUNDLE_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v0.json"
)
PROTOCOL_BUNDLE_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v0.json"
)

V1_PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v1.json"
)
V1_CONSUMER_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
V1_CUSTODY_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_LEGACY_BYTE_CUSTODY_CONTRACT_20260711_v1.json"
)
V1_REVIEW_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_INDEPENDENT_REVIEW_20260711_v1.json"
)
AUTHORITY_REL = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
MAINTENANCE_REL = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
REGISTRY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"

EXPECTED_GIT_BLOBS = {
    AUTHORITY_REL: "d46c5fb1966dcefc6b923776b7d94c4f5009b889",
    MAINTENANCE_REL: "dca311d6abe38a872495c07f302d13ad886c0232",
    REGISTRY_REL: "e6c5b3773dccd92fde9c0a8d486a56f993d6b235",
}
EXPECTED_SHA256 = {
    AUTHORITY_REL: "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
    MAINTENANCE_REL: "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
    REGISTRY_REL: "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
    V1_PACKET_REL: "41994b0c1703d7f7f7ff7aeda217900a3136489f070ae55a88f2db10a13d12c0",
    V1_CONSUMER_REL: "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
    V1_CUSTODY_REL: "bc35c992c9b9fd7dd9c2e84ed6d5b89463b3ce8eb13dc2f7c7d1c539b4d23ce9",
    V1_REVIEW_REL: "4b99d6d3801a8bbd2f918311116dfdfce8ef595f7c0e1b629bc3595820612dca",
}

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
PACKET_TARGET = "prepare_loop_control_registry_sharding_execution_readiness_packet_v0"
REVIEW_TARGET = "review_loop_control_registry_sharding_execution_readiness_packet_v0"

REGISTRY_SIZE_BYTES = 52_340_650
ROOT_FIELD_RECORD_COUNT = 4_152
WORKSTREAM_RECORD_COUNT = 539
TOTAL_RECORD_COUNT = 4_691
CONSUMER_COUNT = 496
CONTROL_COUNT = 52
AUTHORITY_COMMITMENT_SHA256 = "fd4348411236648d6216900eced59524b87c561bfa0d36186cf4c4d19a2e6b34"
RECORD_IDENTITY_ROOT_SHA256 = "67a23fda6348a2a6e12e4c2af775d115c692ecbe4d0650f0844a982d869e112d"
IDENTITY_PAYLOAD_POINTER_ROOT_SHA256 = "a97799ea412006dde3c259b718b10aad9dee7012181611f3f1d5f1a1e821a967"
ORIGINAL_POINTER_ROOT_SHA256 = "219f4bc866b731b74ef50a439b6a869d8add33c6c5ce8e83a621115c1649c6bf"

PROTOTYPE_ROOT = "formal/scratch/loop_control_registry_v1_prototype/<run_id>"
FORBIDDEN_PRODUCTION_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
]


class ReadinessPacketError(ValueError):
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
        raise ReadinessPacketError(f"missing reviewed source blob: {relative}")
    return result.stdout


def _git_blob_oid(relative: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


@lru_cache(maxsize=1)
def _accepted_inputs() -> dict[str, Any]:
    for path, expected in EXPECTED_SHA256.items():
        actual = _sha256(_git_blob(path))
        if actual != expected:
            raise ReadinessPacketError(f"accepted source SHA-256 drift: {path}")
    for path, expected in EXPECTED_GIT_BLOBS.items():
        if _git_blob_oid(path) != expected:
            raise ReadinessPacketError(f"accepted source Git blob drift: {path}")

    packet = json.loads(_git_blob(V1_PACKET_REL))
    consumer = json.loads(_git_blob(V1_CONSUMER_REL))
    custody = json.loads(_git_blob(V1_CUSTODY_REL))
    review = json.loads(_git_blob(V1_REVIEW_REL))
    maintenance = json.loads(_git_blob(MAINTENANCE_REL))

    if packet["negative_control_count"] != CONTROL_COUNT:
        raise ReadinessPacketError("v1 control-count drift")
    if consumer["consumer_count"] != CONSUMER_COUNT:
        raise ReadinessPacketError("v1 consumer-count drift")
    if packet["record_accounting"]["total_record_count"] != TOTAL_RECORD_COUNT:
        raise ReadinessPacketError("v1 record-accounting drift")
    if custody["compatibility_reconstruction"]["decompressed_sha256"] != EXPECTED_SHA256[REGISTRY_REL]:
        raise ReadinessPacketError("v1 byte-custody source drift")
    if review["accepted_scope"]["migration_execution_readiness"] is not False:
        raise ReadinessPacketError("v1 review unexpectedly authorizes execution readiness")
    if maintenance["current_maintenance_target"] != MAINTENANCE_TARGET:
        raise ReadinessPacketError("maintenance target drift")
    if maintenance["scientific_authority"]["current_target"] != SCIENTIFIC_TARGET:
        raise ReadinessPacketError("scientific target drift")
    return {
        "consumer": consumer,
        "custody": custody,
        "maintenance": maintenance,
        "packet": packet,
        "review": review,
    }


def _closed_object(properties: dict[str, Any], *, required: list[str] | None = None) -> dict[str, Any]:
    names = list(properties) if required is None else required
    return {
        "additionalProperties": False,
        "properties": properties,
        "required": names,
        "type": "object",
    }


def _sha_schema(*, const: str | None = None) -> dict[str, Any]:
    schema: dict[str, Any] = {"pattern": "^[0-9a-f]{64}$", "type": "string"}
    if const is not None:
        schema["const"] = const
    return schema


def _path_schema() -> dict[str, Any]:
    return {
        "minLength": 1,
        "not": {"pattern": "(^|/)(\\.\\.?)(/|$)|\\\\|^[A-Za-z]:"},
        "type": "string",
    }


def _source_identity_schema() -> dict[str, Any]:
    return _closed_object(
        {
            "git_blob": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
            "path": _path_schema(),
            "sha256": _sha_schema(),
            "size_bytes": {"minimum": 0, "type": "integer"},
            "source_commit": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
        }
    )


def _current_projection_schema() -> dict[str, Any]:
    blocker = _closed_object(
        {
            "evidence_pointer": _path_schema(),
            "row_id": {"minLength": 1, "type": "string"},
            "status": {
                "enum": ["blocked", "missing", "not_assessed", "partial"],
                "type": "string",
            },
        }
    )
    artifact = _closed_object(
        {
            "artifact_id": {"minLength": 1, "type": "string"},
            "git_blob": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
            "path": _path_schema(),
            "provenance_kind": {"minLength": 1, "type": "string"},
            "role": {"minLength": 1, "type": "string"},
            "sha256": _sha_schema(),
            "size_bytes": {"minimum": 0, "type": "integer"},
            "source_commit": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
        }
    )
    nonpromotion_names = [
        "C_k_action_embedding_authorized",
        "ccft_resumed",
        "cross_sector_coupling_claim_authorized",
        "level_four_or_five_authorized",
        "master_action_promoted",
        "physical_calibration_authorized",
        "pillar_or_seam_admissibility_claimed",
        "unit_closure_claimed",
    ]
    return {
        "$id": "https://toe.local/schema/loop-control-current-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "active_blockers": {"items": blocker, "type": "array", "uniqueItems": True},
                "active_scientific_workstream": _closed_object(
                    {
                        "active_lane": {"minLength": 1, "type": "string"},
                        "authorized_target": {"minLength": 1, "type": "string"},
                        "claim_ceiling_level": {"minimum": 0, "type": "integer"},
                        "claim_status": {"minLength": 1, "type": "string"},
                        "consumed_target": {"minLength": 1, "type": "string"},
                        "consumed_target_kind": {"minLength": 1, "type": "string"},
                        "live_lane": {"minLength": 1, "type": "string"},
                        "original_json_pointer": {"pattern": "^/", "type": "string"},
                        "packet_result": {"minLength": 1, "type": "string"},
                        "queue_scope": {"minLength": 1, "type": "string"},
                        "record_id": {"pattern": "^lcr1:[0-9a-f]{64}$", "type": "string"},
                        "report": _path_schema(),
                        "selected_next_target": {"minLength": 1, "type": "string"},
                        "selected_next_target_kind": {"minLength": 1, "type": "string"},
                        "status": {"minLength": 1, "type": "string"},
                        "strict_packet_result": {"minLength": 1, "type": "string"},
                        "workstream_id": {"minLength": 1, "type": "string"},
                    }
                ),
                "claim_ceiling": _closed_object(
                    {
                        "level": {"minimum": 0, "type": "integer"},
                        "status": {"minLength": 1, "type": "string"},
                        "strict_packet_result": {"minLength": 1, "type": "string"},
                    }
                ),
                "current_artifacts": {"items": artifact, "type": "array", "uniqueItems": True},
                "history_index_pointer": _closed_object(
                    {
                        "path": _path_schema(),
                        "schema_id": {"const": "LOOP_CONTROL_HISTORY_INDEX_v1", "type": "string"},
                        "sha256": _sha_schema(),
                    }
                ),
                "maintenance_authority": _closed_object(
                    {
                        "current_maintenance_target": {"minLength": 1, "type": "string"},
                        "current_maintenance_target_kind": {"minLength": 1, "type": "string"},
                        "current_maintenance_target_status": {"minLength": 1, "type": "string"},
                        "evidence": _closed_object(
                            {"path": _path_schema(), "sha256": _sha_schema()}
                        ),
                    }
                ),
                "nonpromotion_assertions": _closed_object(
                    {
                        name: {"enum": ["no", "yes"], "type": "string"}
                        for name in nonpromotion_names
                    }
                ),
                "projection_version": {"const": 1, "type": "integer"},
                "revision": {"minimum": 0, "type": "integer"},
                "schema_id": {"const": "LOOP_CONTROL_CURRENT_v1", "type": "string"},
                "scientific_authority": _closed_object(
                    {
                        "active_lane": {"minLength": 1, "type": "string"},
                        "authority_commitment_sha256": _sha_schema(),
                        "current_target": {"minLength": 1, "type": "string"},
                        "current_target_kind": {"minLength": 1, "type": "string"},
                        "previous_target": {"minLength": 1, "type": "string"},
                        "workstream_id": {"minLength": 1, "type": "string"},
                    }
                ),
                "source_legacy_identity": _source_identity_schema(),
                "status": {
                    "const": "SHADOW_PROTOTYPE_NONAUTHORITATIVE",
                    "type": "string",
                },
            }
        ),
    }


def _history_record_schema() -> dict[str, Any]:
    return {
        "$id": "https://toe.local/schema/loop-control-history-record-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "identical_occurrence_ordinal": {"minimum": 0, "type": "integer"},
                "logical_key": {"minLength": 1, "type": "string"},
                "original_json_pointer": {"pattern": "^/", "type": "string"},
                "payload_canonical_json_utf8_base64": {
                    "contentEncoding": "base64",
                    "minLength": 4,
                    "type": "string",
                },
                "payload_kind": {
                    "enum": ["ARRAY", "BOOLEAN", "NULL", "NUMBER", "OBJECT", "STRING"],
                    "type": "string",
                },
                "payload_sha256": _sha_schema(),
                "payload_size_bytes": {"minimum": 1, "type": "integer"},
                "record_class": {"enum": ["ROOT_FIELD", "WORKSTREAM"], "type": "string"},
                "record_id": {"pattern": "^lcr1:[0-9a-f]{64}$", "type": "string"},
                "record_version": {"const": 1, "type": "integer"},
                "schema_id": {"const": "LOOP_CONTROL_HISTORY_RECORD_v1", "type": "string"},
                "source_git_blob": {"const": EXPECTED_GIT_BLOBS[REGISTRY_REL], "type": "string"},
                "source_path": {"const": REGISTRY_REL, "type": "string"},
            }
        ),
    }


def _history_index_schema() -> dict[str, Any]:
    shard = _closed_object(
        {
            "closed": {"const": True, "type": "boolean"},
            "first_record_id": {"pattern": "^lcr1:[0-9a-f]{64}$", "type": "string"},
            "last_record_id": {"pattern": "^lcr1:[0-9a-f]{64}$", "type": "string"},
            "path": _path_schema(),
            "record_count": {"minimum": 1, "type": "integer"},
            "record_id_root_sha256": _sha_schema(),
            "sequence_index": {"minimum": 0, "type": "integer"},
            "sha256": _sha_schema(),
            "shard_id": {"pattern": "^lcs1:[0-9a-f]{64}$", "type": "string"},
            "uncompressed_size_bytes": {"maximum": 5_242_880, "minimum": 1, "type": "integer"},
        }
    )
    pointer = _closed_object(
        {"path": _path_schema(), "schema_id": {"minLength": 1, "type": "string"}, "sha256": _sha_schema()}
    )
    return {
        "$id": "https://toe.local/schema/loop-control-history-index-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "consumer_source_map_pointer": pointer,
                "custody_manifest_pointer": pointer,
                "index_version": {"const": 1, "type": "integer"},
                "record_accounting": _closed_object(
                    {
                        "authority_commitment_sha256": _sha_schema(const=AUTHORITY_COMMITMENT_SHA256),
                        "full_record_identity_root_sha256": _sha_schema(const=RECORD_IDENTITY_ROOT_SHA256),
                        "identity_payload_pointer_root_sha256": _sha_schema(const=IDENTITY_PAYLOAD_POINTER_ROOT_SHA256),
                        "original_pointer_set_sha256": _sha_schema(const=ORIGINAL_POINTER_ROOT_SHA256),
                        "root_field_record_count": {"const": ROOT_FIELD_RECORD_COUNT, "type": "integer"},
                        "total_record_count": {"const": TOTAL_RECORD_COUNT, "type": "integer"},
                        "workstream_record_count": {"const": WORKSTREAM_RECORD_COUNT, "type": "integer"},
                    }
                ),
                "record_identity_contract": _closed_object(
                    {
                        "digest": {"const": "FULL_SHA256_64_HEX_NO_TRUNCATION", "type": "string"},
                        "prefix": {"const": "lcr1:", "type": "string"},
                        "preimage_version": {"const": "LOOP_CONTROL_RECORD_ID_v1", "type": "string"},
                    }
                ),
                "schema_id": {"const": "LOOP_CONTROL_HISTORY_INDEX_v1", "type": "string"},
                "shard_count": {"minimum": 1, "type": "integer"},
                "shards": {"items": shard, "minItems": 1, "type": "array", "uniqueItems": True},
                "sharding_contract": _closed_object(
                    {
                        "maximum_uncompressed_shard_bytes": {"const": 5_242_880, "type": "integer"},
                        "placement": {
                            "const": "SORT_FULL_RECORD_ID_THEN_GREEDILY_APPEND_COMPLETE_JSONL_LINES",
                            "type": "string",
                        },
                        "record_set_coverage": {
                            "const": "CONCATENATED_SHARD_RECORD_IDS_EQUAL_COMPLETE_GLOBALLY_SORTED_RECORD_ID_SET",
                            "type": "string",
                        },
                    }
                ),
                "source_registry_identity": _source_identity_schema(),
                "status": {"const": "SHADOW_PROTOTYPE_NONAUTHORITATIVE_CLOSED_HISTORY", "type": "string"},
            }
        ),
    }


def _consumer_map_schema() -> dict[str, Any]:
    consumer = _closed_object(
        {
            "access_operation": {
                "enum": ["DYNAMIC_READER", "PATH_REFERENCE_ONLY", "STATIC_READER_CANDIDATE", "WRITER_AND_READER"],
                "type": "string",
            },
            "classification_confidence": {
                "enum": [
                    "INDEPENDENT_REVIEW_IDENTIFIED_NONLITERAL_READER",
                    "LEXICAL_READER_EVIDENCE_RUNTIME_TRACE_PENDING",
                    "LEXICAL_REFERENCE_NOT_RUNTIME_PROOF",
                    "STATIC_LITERAL_AND_WRITE_ENTRYPOINT",
                ],
                "type": "string",
            },
            "consumer_id": {"pattern": "^lcc1:[0-9a-f]{64}$", "type": "string"},
            "consumer_role": {
                "enum": [
                    "ACTIVE_TOOL_OR_AUTOMATION",
                    "DOCUMENTATION_ONLY_REFERENCE",
                    "HISTORICAL_OR_STRUCTURED_REFERENCE",
                    "LEAN_CONSTANT_OR_CERTIFICATE_REFERENCE",
                    "TEST_ONLY_CONSUMER",
                ],
                "type": "string",
            },
            "discovery_methods": {"items": {"minLength": 1, "type": "string"}, "minItems": 1, "type": "array", "uniqueItems": True},
            "evidence_line_numbers": {"items": {"minimum": 1, "type": "integer"}, "type": "array", "uniqueItems": True},
            "git_blob": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
            "language": {"minLength": 1, "type": "string"},
            "migration_batch": {"minLength": 1, "type": "string"},
            "path": _path_schema(),
            "runtime_disposition": {
                "enum": ["OBSERVED_RUNTIME", "PROVED_NONRUNTIME_BY_CLASSIFICATION", "PENDING"],
                "type": "string",
            },
            "runtime_trace_required": {"type": "boolean"},
            "schema_or_ordering_assumption": {"minLength": 1, "type": "string"},
            "source_sha256": _sha_schema(),
            "source_size_bytes": {"minimum": 0, "type": "integer"},
        }
    )
    return {
        "$id": "https://toe.local/schema/loop-control-consumer-source-map-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "baseline": _closed_object(
                    {
                        "consumer_count": {"const": CONSUMER_COUNT, "type": "integer"},
                        "path": {"const": V1_CONSUMER_REL, "type": "string"},
                        "sha256": _sha_schema(const=EXPECTED_SHA256[V1_CONSUMER_REL]),
                        "source_commit": {"const": SOURCE_COMMIT, "type": "string"},
                    }
                ),
                "consumers": {"items": consumer, "minItems": 1, "type": "array", "uniqueItems": True},
                "current_scan": _closed_object(
                    {
                        "added_consumer_ids": {"items": {"pattern": "^lcc1:[0-9a-f]{64}$", "type": "string"}, "type": "array", "uniqueItems": True},
                        "changed_consumer_ids": {"items": {"pattern": "^lcc1:[0-9a-f]{64}$", "type": "string"}, "type": "array", "uniqueItems": True},
                        "consumer_count": {"minimum": 1, "type": "integer"},
                        "removed_consumer_ids": {"items": {"pattern": "^lcc1:[0-9a-f]{64}$", "type": "string"}, "type": "array", "uniqueItems": True},
                        "source_commit": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
                        "unclassified_count": {"const": 0, "type": "integer"},
                    }
                ),
                "schema_id": {"const": "LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2", "type": "string"},
                "status": {"const": "STATIC_AND_RUNTIME_DISPOSITIONS_REQUIRED_BEFORE_CUTOVER", "type": "string"},
            }
        ),
    }


def _custody_manifest_schema() -> dict[str, Any]:
    return {
        "$id": "https://toe.local/schema/loop-control-byte-custody-manifest-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "contract_pointer": _closed_object(
                    {"path": {"const": V1_CUSTODY_REL, "type": "string"}, "sha256": _sha_schema(const=EXPECTED_SHA256[V1_CUSTODY_REL])}
                ),
                "external_binding": _closed_object(
                    {
                        "accepted_guardrail_packet_sha256": _sha_schema(const=EXPECTED_SHA256[V1_PACKET_REL]),
                        "accepted_guardrail_review_sha256": _sha_schema(const=EXPECTED_SHA256[V1_REVIEW_REL]),
                    }
                ),
                "generation_provenance": _closed_object(
                    {
                        "detached_checkout_commit": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
                        "generator_sha256": _sha_schema(),
                        "run_id": {"pattern": "^[A-Za-z0-9._-]+$", "type": "string"},
                    }
                ),
                "gzip_profile": _closed_object(
                    {
                        "algorithm": {"const": "RFC1952_GZIP_SINGLE_MEMBER_DEFLATE", "type": "string"},
                        "cm": {"const": 8, "type": "integer"},
                        "compression_level": {"const": 9, "type": "integer"},
                        "flg": {"const": 0, "type": "integer"},
                        "member_count": {"const": 1, "type": "integer"},
                        "mtime": {"const": 0, "type": "integer"},
                        "os": {"const": 255, "type": "integer"},
                        "require_crc32_and_isize": {"const": True, "type": "boolean"},
                        "path": _path_schema(),
                        "trailing_byte_count": {"const": 0, "type": "integer"},
                        "xfl": {"const": 2, "type": "integer"},
                    }
                ),
                "manifest_version": {"const": 1, "type": "integer"},
                "payload_identity": _closed_object(
                    {
                        "compressed_sha256": _sha_schema(),
                        "compressed_size_bytes": {"minimum": 1, "type": "integer"},
                        "path": _path_schema(),
                    }
                ),
                "reconstruction_requirement": _closed_object(
                    {
                        "byte_identical": {"const": True, "type": "boolean"},
                        "decompressed_sha256": _sha_schema(const=EXPECTED_SHA256[REGISTRY_REL]),
                        "decompressed_size_bytes": {"const": REGISTRY_SIZE_BYTES, "type": "integer"},
                    }
                ),
                "schema_id": {"const": "LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1", "type": "string"},
                "source_identity": _source_identity_schema(),
                "status": {"const": "PROTOTYPE_CUSTODY_PAYLOAD_VERIFIED_NONAUTHORITATIVE", "type": "string"},
            }
        ),
    }


def _reconstruction_result_schema() -> dict[str, Any]:
    return {
        "$id": "https://toe.local/schema/loop-control-legacy-reconstruction-result-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "byte_comparison": _closed_object(
                    {
                        "byte_identical": {"const": True, "type": "boolean"},
                        "sha256_match": {"const": True, "type": "boolean"},
                        "size_match": {"const": True, "type": "boolean"},
                    }
                ),
                "clean_checkout_evidence": _closed_object(
                    {
                        "commit": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
                        "detached": {"const": True, "type": "boolean"},
                        "worktree_clean_after": {"const": True, "type": "boolean"},
                        "worktree_clean_before": {"const": True, "type": "boolean"},
                    }
                ),
                "cleanup": _closed_object(
                    {
                        "runtime_output_retained": {"const": False, "type": "boolean"},
                        "temporary_output_removed": {"const": True, "type": "boolean"},
                    }
                ),
                "custody_payload_identity": _closed_object(
                    {"path": _path_schema(), "sha256": _sha_schema(), "size_bytes": {"minimum": 1, "type": "integer"}}
                ),
                "reconstruction_identity": _closed_object(
                    {
                        "path": _path_schema(),
                        "sha256": _sha_schema(const=EXPECTED_SHA256[REGISTRY_REL]),
                        "size_bytes": {"const": REGISTRY_SIZE_BYTES, "type": "integer"},
                    }
                ),
                "report_version": {"const": 1, "type": "integer"},
                "schema_id": {"const": "LOOP_CONTROL_COMPATIBILITY_RECONSTRUCTION_REPORT_v1", "type": "string"},
                "semantic_history_comparison": _closed_object(
                    {"record_count_match": {"const": True, "type": "boolean"}, "record_root_match": {"const": True, "type": "boolean"}}
                ),
                "source_identity": _source_identity_schema(),
                "status": {"const": "BYTE_EXACT_RECONSTRUCTION_VERIFIED", "type": "string"},
                "validator_identity": _closed_object(
                    {"path": _path_schema(), "sha256": _sha_schema(), "version": {"minLength": 1, "type": "string"}}
                ),
            }
        ),
    }


def _shadow_trace_schema() -> dict[str, Any]:
    return {
        "$id": "https://toe.local/schema/loop-control-runtime-shadow-trace-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "access_granularity": {"enum": ["EXACT_FIELDS", "ROOT_DOCUMENT"], "type": "string"},
                "candidate_result_sha256": _sha_schema(),
                "comparison_mode": {"const": "CANONICAL_TYPED_ENVELOPE", "type": "string"},
                "consumer_id": {"pattern": "^lcc1:[0-9a-f]{64}$", "type": "string"},
                "consumer_path": _path_schema(),
                "consumer_source_sha256": _sha_schema(),
                "fields_accessed": {"items": {"pattern": "^/", "type": "string"}, "type": "array", "uniqueItems": True},
                "legacy_result_sha256": _sha_schema(),
                "operation_id": {"minLength": 1, "type": "string"},
                "operation_type": {
                    "enum": [
                        "DIRECT_MONOLITH_READ",
                        "DIRECT_MONOLITH_WRITE",
                        "GET_CURRENT_MAINTENANCE_TARGET",
                        "GET_CURRENT_TARGET",
                        "GET_CURRENT_WORKSTREAM",
                        "GET_HISTORICAL_RECORD",
                        "ITER_HISTORICAL_RECORDS",
                        "LOAD_CURRENT_PROJECTION",
                        "RECONSTRUCT_LEGACY_REGISTRY",
                        "VERIFY_REGISTRY_INTEGRITY",
                        "WRITE_CURRENT_PROJECTION",
                    ],
                    "type": "string",
                },
                "resolved_registry_path": _path_schema(),
                "run_id": {"pattern": "^[A-Za-z0-9._-]+$", "type": "string"},
                "runtime_entrypoint": {"minLength": 1, "type": "string"},
                "semantic_parity": {"type": "boolean"},
                "source_commit": {"pattern": "^[0-9a-f]{40}$", "type": "string"},
                "trace_id": {"pattern": "^lct1:[0-9a-f]{64}$", "type": "string"},
                "trace_schema_id": {"const": "LOOP_CONTROL_SHADOW_TRACE_EVENT_v1", "type": "string"},
                "write_attempted": {"type": "boolean"},
                "write_paths": {"items": _path_schema(), "type": "array", "uniqueItems": True},
            }
        ),
    }


def _shadow_trace_manifest_schema() -> dict[str, Any]:
    return {
        "$id": "https://toe.local/schema/loop-control-shadow-trace-manifest-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "consumer_scan_sha256": _sha_schema(),
                "event_count": {"minimum": 1, "type": "integer"},
                "event_jsonl_sha256": _sha_schema(),
                "migration_batch_coverage_complete": {"type": "boolean"},
                "operation_class_coverage_complete": {"type": "boolean"},
                "required_consumer_count": {"minimum": 1, "type": "integer"},
                "required_consumers_observed": {"minimum": 0, "type": "integer"},
                "run_id": {"pattern": "^[A-Za-z0-9._-]+$", "type": "string"},
                "schema_id": {"const": "LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v1", "type": "string"},
                "semantic_mismatch_count": {"const": 0, "type": "integer"},
                "status": {"const": "COMPLETE_PARITY_REQUIRED_FOR_MIGRATION_READINESS", "type": "string"},
                "unclassified_consumer_count": {"const": 0, "type": "integer"},
                "unobserved_required_consumer_count": {"const": 0, "type": "integer"},
            }
        ),
    }


def _validation_report_schema() -> dict[str, Any]:
    issue = _closed_object(
        {
            "artifact_path": _path_schema(),
            "control_id": {"pattern": "^REGISTRY-V1-NC-[0-9]{3}$", "type": ["string", "null"]},
            "error_code": {"pattern": "^V1-E-[A-Z0-9-]+$", "type": "string"},
            "json_pointer": {"type": "string"},
            "message": {"minLength": 1, "type": "string"},
        }
    )
    return {
        "$id": "https://toe.local/schema/loop-control-validation-report-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "candidate_root_sha256": _sha_schema(),
                "issues": {"items": issue, "type": "array"},
                "passed": {"type": "boolean"},
                "profile": {"enum": ["CUTOVER_ELIGIBILITY", "PROTOTYPE_INTEGRITY", "SHADOW_PARITY", "WRITE_SAFETY"], "type": "string"},
                "schema_id": {"const": "LOOP_CONTROL_VALIDATION_REPORT_v1", "type": "string"},
                "trust_anchor_sha256": _sha_schema(),
            }
        ),
    }


def _control_harness_report_schema() -> dict[str, Any]:
    profile = _closed_object(
        {
            "baseline_after_passed": {"const": True, "type": "boolean"},
            "baseline_before_passed": {"const": True, "type": "boolean"},
            "control_count": {"minimum": 0, "type": "integer"},
            "controls_passed": {"minimum": 0, "type": "integer"},
            "profile": {"enum": ["CUTOVER_ELIGIBILITY", "PROTOTYPE_INTEGRITY", "SHADOW_PARITY", "WRITE_SAFETY"], "type": "string"},
        }
    )
    return {
        "$id": "https://toe.local/schema/loop-control-control-harness-report-v1.schema.json",
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        **_closed_object(
            {
                "base_candidate_sha256_after": _sha_schema(),
                "base_candidate_sha256_before": _sha_schema(),
                "control_count": {"const": CONTROL_COUNT, "type": "integer"},
                "controls_passed": {"const": CONTROL_COUNT, "type": "integer"},
                "profile_reports": {"items": profile, "maxItems": 4, "minItems": 4, "type": "array", "uniqueItems": True},
                "schema_id": {"const": "LOOP_CONTROL_CONTROL_HARNESS_REPORT_v1", "type": "string"},
                "status": {"const": "ALL_ISOLATED_CONTROLS_PASSED", "type": "string"},
            }
        ),
    }


@lru_cache(maxsize=1)
def build_schema_bundle() -> dict[str, Any]:
    _accepted_inputs()
    return {
        "canonical_instance_bytes": {
            "allow_nan": False,
            "duplicate_keys_rejected_before_schema_evaluation": True,
            "encoding": "UTF-8_NO_BOM",
            "final_newline": "EXACTLY_ONE_LF",
            "key_order": "LEXICOGRAPHIC",
            "line_endings": "LF_ONLY",
            "unknown_fields_rejected": True,
        },
        "draft": "JSON_SCHEMA_2020_12",
        "external_value_constraints": {
            "current_projection./maintenance_authority/current_maintenance_target": MAINTENANCE_TARGET,
            "current_projection./scientific_authority/current_target": SCIENTIFIC_TARGET,
            "current_projection./scientific_authority/authority_commitment_sha256": AUTHORITY_COMMITMENT_SHA256,
            "current_projection./source_legacy_identity/sha256": EXPECTED_SHA256[REGISTRY_REL],
            "current_projection./nonpromotion_assertions/*": "no",
        },
        "schema_count": 10,
        "schema_id": "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v0",
        "schemas": {
            "compatibility_reconstruction_result": _reconstruction_result_schema(),
            "control_harness_report": _control_harness_report_schema(),
            "consumer_source_map": _consumer_map_schema(),
            "current_projection": _current_projection_schema(),
            "history_index": _history_index_schema(),
            "history_shard_record": _history_record_schema(),
            "legacy_byte_custody_manifest": _custody_manifest_schema(),
            "runtime_shadow_trace_event": _shadow_trace_schema(),
            "runtime_shadow_trace_manifest": _shadow_trace_manifest_schema(),
            "validation_report": _validation_report_schema(),
        },
        "status": "EXACT_CLOSED_SCHEMAS_FROZEN_AS_PREPARATION_CONTRACT_NO_PRODUCTION_VALIDATOR_OR_ARTIFACT",
    }


def _interface_contract() -> dict[str, Any]:
    return {
        "candidate_expected_values_are_authoritative": False,
        "error_result": _closed_object(
            {
                "artifact_path": _path_schema(),
                "control_id": {"pattern": "^REGISTRY-V1-NC-[0-9]{3}$", "type": ["string", "null"]},
                "error_code": {"pattern": "^V1-E-[A-Z0-9-]+$", "type": "string"},
                "json_pointer": {"type": "string"},
                "message": {"minLength": 1, "type": "string"},
            }
        ),
        "external_trust_anchor_source": {
            "accepted_v1_guardrail_sha256": EXPECTED_SHA256[V1_PACKET_REL],
            "accepted_v1_review_sha256": EXPECTED_SHA256[V1_REVIEW_REL],
            "source_commit": SOURCE_COMMIT,
        },
        "frozen_functions": [
            "strict_load_json(raw: bytes, artifact_kind: ArtifactKind) -> JsonValue",
            "strict_iter_jsonl(stream: BinaryIO, maximum_bytes: int) -> Iterator[HistoryRecord]",
            "load_reviewed_trust_anchors(packet_path: Path, expected_packet_sha256: str) -> RegistryTrustAnchors",
            "validate_prototype_integrity(source: ArtifactSource, anchors: RegistryTrustAnchors) -> ValidationReport",
            "validate_write_safety(source: ArtifactSource, anchors: RegistryTrustAnchors, writer_probe: WriterProbe) -> ValidationReport",
            "validate_shadow_parity(source: ArtifactSource, anchors: RegistryTrustAnchors, trace_manifest: ShadowTraceManifest) -> ValidationReport",
            "validate_cutover_eligibility(source: ArtifactSource, anchors: RegistryTrustAnchors, trace_manifest: ShadowTraceManifest) -> ValidationReport",
            "reconstruct_and_verify_legacy(candidate_root: Path, output: BinaryIO, anchors: ReviewedTrustAnchors) -> ReconstructionReport",
            "require_valid(report: ValidationReport) -> None",
        ],
        "integrity_bypass_parameter_allowed": False,
        "profile_selected_by_caller_not_candidate": True,
        "profile_specific_entrypoints": [
            "validate_prototype_integrity(candidate_root: Path, anchors: ReviewedTrustAnchors) -> ValidationReport",
            "validate_write_safety(candidate_root: Path, anchors: ReviewedTrustAnchors) -> ValidationReport",
            "validate_shadow_parity(candidate_root: Path, anchors: ReviewedTrustAnchors) -> ValidationReport",
            "validate_cutover_eligibility(candidate_root: Path, anchors: ReviewedTrustAnchors) -> ValidationReport",
        ],
        "module_path_after_separate_execution_authorization": "formal/python/toe/loop_control_registry_v1_validator.py",
        "read_only": True,
        "report_contract": {
            "all_error_codes_sorted": True,
            "candidate_root_sha256": "REQUIRED",
            "errors": "ORDERED_TYPED_LIST",
            "passed": "TRUE_ONLY_WHEN_ERRORS_EMPTY",
            "trust_anchor_sha256": "REQUIRED_EXTERNAL_VALUE",
        },
        "write_interfaces_separate": True,
    }


@lru_cache(maxsize=1)
def build_protocol_bundle() -> dict[str, Any]:
    accepted = _accepted_inputs()
    controls = []
    for row in accepted["packet"]["negative_controls"]:
        if row["control_id"] in {"REGISTRY-V1-NC-041", "REGISTRY-V1-NC-042"}:
            profile = "WRITE_SAFETY"
        elif row["control_id"] in {"REGISTRY-V1-NC-045", "REGISTRY-V1-NC-046"}:
            profile = "SHADOW_PARITY"
        elif row["control_id"] == "REGISTRY-V1-NC-044":
            profile = "CUTOVER_ELIGIBILITY"
        else:
            profile = "PROTOTYPE_INTEGRITY"
        mutation = row["mutation"]
        if any(token in mutation for token in ("gzip", "custody")):
            artifact_kind = "BYTE_CUSTODY"
        elif any(token in mutation for token in ("consumer", "runtime_trace", "monolith_reader")):
            artifact_kind = "CONSUMER_OR_TRACE"
        elif any(token in mutation for token in ("projection", "authority", "target", "claim_ceiling", "blocker", "nonpromotion")):
            artifact_kind = "CURRENT_PROJECTION"
        elif "index" in mutation or "shard" in mutation or "range" in mutation:
            artifact_kind = "HISTORY_INDEX_OR_SHARD"
        else:
            artifact_kind = "CANDIDATE_BUNDLE"
        controls.append(
            {
                "artifact_kind": artifact_kind,
                "baseline_candidate_recreated_before_mutation": True,
                "control_id": row["control_id"],
                "execution_status": "NOT_EXECUTED_PREPARATION_ONLY",
                "expected_exact_error_set": [row["expected_error_code"]],
                "expected_decision": "REJECT",
                "fixture_isolation": "FRESH_TEMPORARY_CANDIDATE_TREE",
                "mutation": mutation,
                "mutation_precondition": f"{profile}_POSITIVE_BASELINE_PASSES",
                "mutator_entrypoint": f"mutate_{mutation}(overlay: ArtifactOverlay) -> None",
                "rebind_candidate_internal_hashes": "rebound" in mutation,
                "requires_runtime_trace": row["control_id"] in {"REGISTRY-V1-NC-044", "REGISTRY-V1-NC-046"},
                "requires_write_sandbox": row["control_id"] in {"REGISTRY-V1-NC-041", "REGISTRY-V1-NC-042"},
                "subsequent_controls_receive_unmodified_baseline": True,
                "validator_profile": profile,
                "v0_false_acceptance_regression": row["v0_false_acceptance_regression"],
            }
        )
    if len(controls) != CONTROL_COUNT:
        raise ReadinessPacketError("execution-control contract count drift")

    paths = {
        "compatibility_reconstruction": f"{PROTOTYPE_ROOT}/compat/LOOP_CONTROL_REGISTRY_v0.reconstructed.json",
        "consumer_source_map": f"{PROTOTYPE_ROOT}/consumers/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2.json",
        "current_projection": f"{PROTOTYPE_ROOT}/projection/LOOP_CONTROL_CURRENT_v1.prototype.json",
        "custody_manifest": f"{PROTOTYPE_ROOT}/custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1.json",
        "custody_payload": f"{PROTOTYPE_ROOT}/custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
        "history_index": f"{PROTOTYPE_ROOT}/history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json",
        "history_shards": f"{PROTOTYPE_ROOT}/history/shards/LOOP_CONTROL_HISTORY_*.jsonl",
        "reconstruction_result": f"{PROTOTYPE_ROOT}/compat/LOOP_CONTROL_LEGACY_RECONSTRUCTION_RESULT_v1.json",
        "runtime_shadow_trace": f"{PROTOTYPE_ROOT}/traces/LOOP_CONTROL_RUNTIME_SHADOW_TRACE_v1.jsonl",
        "runtime_shadow_trace_manifest": f"{PROTOTYPE_ROOT}/traces/LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v1.json",
        "control_harness_report": f"{PROTOTYPE_ROOT}/validation/LOOP_CONTROL_CONTROL_HARNESS_REPORT_v1.json",
        "validation_report": f"{PROTOTYPE_ROOT}/validation/LOOP_CONTROL_REGISTRY_V1_VALIDATION_REPORT.json",
    }
    return {
        "authorization": {
            "consumer_migration_authorized": False,
            "custody_payload_creation_authorized_now": False,
            "monolith_modification_or_retirement_authorized": False,
            "production_validator_implementation_authorized_now": False,
            "prototype_artifact_creation_authorized_now": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
        },
        "byte_custody_execution_procedure": {
            "acceptance": {
                "byte_identical": True,
                "decompressed_sha256": EXPECTED_SHA256[REGISTRY_REL],
                "decompressed_size_bytes": REGISTRY_SIZE_BYTES,
                "detached_clean_checkout_required": True,
                "reconstructed_sha256": EXPECTED_SHA256[REGISTRY_REL],
            },
            "procedure": [
                "READ_FROZEN_SOURCE_AS_GIT_BLOB_FROM_REVIEWED_COMMIT",
                "STREAM_ONE_RFC1952_MEMBER_WITH_DEFLATE_LEVEL_9_MTIME_0_FLG_0_XFL_2_OS_255",
                "RECORD_COMPRESSED_SIZE_AND_SHA256_IN_CLOSED_CUSTODY_MANIFEST",
                "REJECT_EXTRA_FIELDS_FILENAME_COMMENT_MULTIPLE_MEMBERS_OR_TRAILING_BYTES",
                "STREAM_DECOMPRESS_WITH_52340650_BYTE_HARD_LIMIT",
                "COMPARE_DECOMPRESSED_BYTES_AND_SHA256_TO_EXTERNAL_FROZEN_SOURCE",
                "WRITE_COMPATIBILITY_OUTPUT_ONLY_INSIDE_ISOLATED_PROTOTYPE_ROOT",
                "VERIFY_RECONSTRUCTED_BYTES_SHA256_AND_SIZE_IN_DETACHED_CLEAN_CHECKOUT",
                "REMOVE_TEMPORARY_52_MIB_RECONSTRUCTION_AFTER_COMPACT_EVIDENCE_IS_RECORDED",
            ],
            "semantic_equivalence_alone_sufficient": False,
        },
        "failure_and_rollback": {
            "fail_closed_triggers": [
                "SCHEMA_OR_STRICT_PARSE_FAILURE",
                "EXTERNAL_TRUST_ANCHOR_MISMATCH",
                "RECORD_COUNT_OR_ROOT_MISMATCH",
                "CONTROL_DECISION_OR_ERROR_SET_MISMATCH",
                "SHADOW_PARITY_MISMATCH",
                "UNTRACED_REQUIRED_CONSUMER",
                "BYTE_CUSTODY_OR_RECONSTRUCTION_MISMATCH",
                "DIRTY_DETACHED_CHECKOUT",
                "UNEXPECTED_WRITE_OUTSIDE_PROTOTYPE_ROOT",
            ],
            "failed_or_timed_out_run_classification": "INCOMPLETE_OR_FAILED_NEVER_PASS",
            "failure_may_rotate_target_or_authority": False,
            "failure_may_touch_legacy_monolith": False,
            "failure_may_touch_scientific_artifacts": False,
            "rollback_scope": "DELETE_ONLY_FILES_CREATED_UNDER_THE_EXACT_RUN_ID_PROTOTYPE_ROOT",
            "rollback_requires_verified_resolved_path_under_prototype_root": True,
            "rollback_uses_git_history_rewrite": False,
            "in_place_candidate_repair_after_failure_allowed": False,
            "source_and_authority_hashes_rechecked_after_run": True,
            "unexpected_write_outside_prototype_root": "FAIL_CLOSED_AND_REQUIRE_INDEPENDENT_DAMAGE_AUDIT",
        },
        "production_validator_interface": _interface_contract(),
        "validator_engine_and_lock_contract": {
            "direct_requirements_lock_entry_present_at_source_commit": False,
            "duplicate_key_and_nonfinite_checks_are_parser_level_not_schema_only": True,
            "engine": "jsonschema",
            "implementation_blocked_until_direct_lock_and_transitive_closure_reviewed": True,
            "required_draft": "2020-12",
            "required_exact_version": "4.26.0",
            "requirements_path": "requirements.ci.lock",
        },
        "prototype_paths": paths,
        "runtime_shadow_tracing_protocol": {
            "all_496_static_rows_require_final_disposition": True,
            "baseline_count_is_not_an_eternal_current_count": True,
            "baseline_source_map_sha256": EXPECTED_SHA256[V1_CONSUMER_REL],
            "comparison": "LEGACY_AND_NEW_READ_EXECUTED_FOR_SAME_OPERATION_AND_INPUT",
            "consumer_migration_or_cutover_during_trace": False,
            "fresh_full_tree_rescan_and_structured_delta_required": True,
            "result_hash_envelope": "CANONICAL_TYPED_VALUE_OR_TYPED_EXCEPTION_ENVELOPE",
            "coverage_acceptance": [
                "EVERY_RUNTIME_TRACE_REQUIRED_ROW_OBSERVED",
                "EVERY_REMAINING_ROW_PROVED_NONRUNTIME_BY_CLASSIFICATION",
                "ALL_DYNAMIC_PATH_CONSTRUCTION_AND_GLOB_READERS_OBSERVED",
                "ALL_ACTIVE_READER_OPERATION_CLASSES_HAVE_HASH_AND_SEMANTIC_PARITY",
                "ALL_WRITERS_EXERCISED_IN_DRY_RUN_WITH_NO_HISTORY_MUTATION",
                "ZERO_UNCLASSIFIED_ACTIVE_CONSUMERS",
                "ZERO_SEMANTIC_PARITY_MISMATCHES",
            ],
            "unobserved_required_consumer_waiver_allowed": False,
            "required_trace_fields": [
                "trace_schema_id",
                "run_id",
                "trace_id",
                "consumer_id",
                "consumer_path",
                "consumer_source_sha256",
                "operation_id",
                "operation_type",
                "comparison_mode",
                "legacy_result_sha256",
                "candidate_result_sha256",
                "semantic_parity",
                "fields_accessed",
                "access_granularity",
                "write_attempted",
                "write_paths",
                "runtime_entrypoint",
                "resolved_registry_path",
                "source_commit",
            ],
            "trace_output": paths["runtime_shadow_trace"],
        },
        "schema_id": "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v0",
        "status": "EXECUTION_PROTOCOL_FROZEN_PREPARATION_ONLY_NOT_EXECUTED",
        "typed_control_harness": {
            "artifact_overlay_required_to_prevent_mutation_leakage_without_full_copy": True,
            "all_controls_run_against_real_candidate_artifacts": True,
            "base_candidate_hash_rechecked_before_and_after_every_control": True,
            "baseline_candidate_must_pass_before_each_mutation": True,
            "caches_cleared_between_controls": True,
            "control_count": len(controls),
            "controls": controls,
            "execution_complete": False,
            "future_test_path": "formal/python/tests/test_loop_control_registry_v1_production_controls.py",
            "order_independence_required": True,
            "positive_baseline_rerun_after_complete_suite": True,
            "production_validator_exists": False,
            "profile_is_caller_selected_never_candidate_selected": True,
            "validator_profiles": {
                "CUTOVER_ELIGIBILITY": {
                    "extends": "SHADOW_PARITY",
                    "legacy_monolith_readers_required": False,
                    "positive_baseline": "CUTOVER_CANDIDATE_WITH_ZERO_ACTIVE_MONOLITH_READERS",
                },
                "PROTOTYPE_INTEGRITY": {
                    "extends": None,
                    "legacy_monolith_readers_allowed": True,
                    "positive_baseline": "READ_ONLY_PROTOTYPE_WITH_FROZEN_LAYOUT_AND_CUSTODY",
                },
                "SHADOW_PARITY": {
                    "extends": "WRITE_SAFETY",
                    "legacy_monolith_readers_required": True,
                    "positive_baseline": "DUAL_READ_SHADOW_CANDIDATE_WITH_COMPLETE_RUNTIME_TRACE",
                },
                "WRITE_SAFETY": {
                    "extends": "PROTOTYPE_INTEGRITY",
                    "legacy_monolith_readers_allowed": True,
                    "positive_baseline": "PROTOTYPE_WITH_DRY_RUN_CURRENT_WRITER_AND_CLOSED_HISTORY",
                },
            },
        },
    }


@lru_cache(maxsize=1)
def build_packet() -> dict[str, Any]:
    accepted = _accepted_inputs()
    schemas = build_schema_bundle()
    protocol = build_protocol_bundle()
    schema_raw = canonical_json_bytes(schemas)
    protocol_raw = canonical_json_bytes(protocol)
    open_findings = [row for row in accepted["review"]["findings"] if row["status"].startswith("OPEN")]
    return {
        "accepted_v1_input": {
            "consumer_count": CONSUMER_COUNT,
            "control_count": CONTROL_COUNT,
            "guardrail_packet_sha256": EXPECTED_SHA256[V1_PACKET_REL],
            "guardrail_review_sha256": EXPECTED_SHA256[V1_REVIEW_REL],
            "migration_execution_readiness_accepted": False,
            "open_finding_count": len(open_findings),
            "record_count": TOTAL_RECORD_COUNT,
        },
        "authorization": {
            "maintenance_target": MAINTENANCE_TARGET,
            "packet_target_is_current_maintenance_authority": False,
            "prototype_execution_target_selected": False,
            "registry_migration_execution_authorized": False,
            "review_target_recommended_not_selected": REVIEW_TARGET,
            "scientific_target": SCIENTIFIC_TARGET,
        },
        "boundary": {
            "authority_cutover": False,
            "claim_or_blocker_promotion": False,
            "consumer_migration": False,
            "control_harness_executed": False,
            "current_projection_generated": False,
            "custody_payload_created": False,
            "history_index_generated": False,
            "history_shards_generated": False,
            "legacy_monolith_modified_or_retired": False,
            "maintenance_target_rotated": False,
            "maintenance_target_consumed_or_rotated": False,
            "production_reader_or_writer_api_created": False,
            "production_schemas_installed": False,
            "production_validator_or_control_harness_implemented": False,
            "prototype_artifacts_created": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_target_consumed_or_rotated": False,
            "scientific_target_rotated": False,
            "shadow_trace_executed": False,
            "unit_ledger_executed": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "closed_schema_bundle": {
            "path": str(SCHEMA_BUNDLE_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "schema_count": schemas["schema_count"],
            "sha256": _sha256(schema_raw),
        },
        "execution_protocol_bundle": {
            "path": str(PROTOCOL_BUNDLE_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sha256": _sha256(protocol_raw),
            "typed_control_count": protocol["typed_control_harness"]["control_count"],
        },
        "external_trust_anchors": {
            "accepted_source_commit": SOURCE_COMMIT,
            "authority_commitment_sha256": AUTHORITY_COMMITMENT_SHA256,
            "current_authority_sha256": EXPECTED_SHA256[AUTHORITY_REL],
            "full_record_identity_root_sha256": RECORD_IDENTITY_ROOT_SHA256,
            "identity_payload_pointer_root_sha256": IDENTITY_PAYLOAD_POINTER_ROOT_SHA256,
            "maintenance_authority_sha256": EXPECTED_SHA256[MAINTENANCE_REL],
            "original_pointer_set_sha256": ORIGINAL_POINTER_ROOT_SHA256,
            "source_registry_git_blob": EXPECTED_GIT_BLOBS[REGISTRY_REL],
            "source_registry_sha256": EXPECTED_SHA256[REGISTRY_REL],
            "source_registry_size_bytes": REGISTRY_SIZE_BYTES,
        },
        "migration_execution_selection_conditions": [
            "READINESS_PACKET_INDEPENDENTLY_ACCEPTED_WITHOUT_TARGET_ROTATION",
            "CLOSED_SCHEMAS_IMPLEMENTED_AND_INDEPENDENTLY_VALIDATED",
            "PRODUCTION_VALIDATOR_AND_ALL_52_ISOLATED_CONTROLS_PASS",
            "READ_ONLY_PROTOTYPE_ACCOUNTS_FOR_ALL_4691_RECORDS",
            "BYTE_CUSTODY_AND_COMPATIBILITY_RECONSTRUCTION_MATCH_FROZEN_BYTES",
            "ALL_496_CONSUMERS_HAVE_FINAL_STATIC_AND_RUNTIME_DISPOSITIONS",
            "SHADOW_PARITY_HAS_ZERO_UNEXPLAINED_MISMATCHES",
            "RAW_DETACHED_CLEAN_CHECKOUT_REPRODUCES_PROTOTYPE_EVIDENCE",
            "INDEPENDENT_PROTOTYPE_REVIEW_ACCEPTS_ONLY_BOUNDED_MIGRATION_READINESS",
            "SEPARATE_AUTHORITY_PACKET_EXPLICITLY_SELECTS_AN_EXECUTION_TARGET",
        ],
        "readiness_levels": {
            "cutover": {
                "currently_satisfied": False,
                "requirements": [
                    "MIGRATION_EXECUTION_READINESS_INDEPENDENTLY_ACCEPTED",
                    "ZERO_ACTIVE_MONOLITH_READERS",
                    "CONSUMER_MIGRATION_BATCHES_COMPLETE",
                    "SEPARATE_CUTOVER_AUTHORITY_PACKET_ACCEPTED",
                ],
            },
            "migration_execution_selection": {
                "currently_satisfied": False,
                "requirements_source": "migration_execution_selection_conditions",
            },
            "packet_acceptance": {
                "currently_satisfied": False,
                "proves_only": "SCHEMAS_AND_PROTOCOLS_ARE_EXACT_AND_INDEPENDENTLY_REVIEWABLE",
                "requires": "INDEPENDENT_PACKET_REVIEW",
            },
            "read_only_prototype_selection": {
                "currently_satisfied": False,
                "requirements": [
                    "INDEPENDENT_PACKET_REVIEW_ACCEPTED",
                    "SCHEMAS_PASS_METASCHEMA_AND_CLOSURE_AUDITS",
                    "VALIDATOR_ENGINE_DEPENDENCY_DIRECTLY_PINNED_AND_REPRODUCIBLE",
                    "PREPARATION_HASHES_AND_AUTHORITY_TOKENS_UNCHANGED",
                    "SEPARATE_AUTHORITY_PACKET_SELECTS_READ_ONLY_PROTOTYPE_EXECUTION",
                ],
            },
        },
        "packet_id": "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v0",
        "packet_target": PACKET_TARGET,
        "preparation_obligations_frozen": [
            "EXACT_CLOSED_SCHEMAS",
            "PRODUCTION_VALIDATOR_INTERFACES",
            "FIFTY_TWO_CONTROL_EXECUTABLE_HARNESS_CONTRACT",
            "RUNTIME_SHADOW_TRACING_PROTOCOL",
            "BYTE_CUSTODY_PAYLOAD_EXECUTION_PROCEDURE",
            "ISOLATED_PROTOTYPE_ARTIFACT_PATHS",
            "FAILURE_AND_ROLLBACK_RULES",
            "MIGRATION_EXECUTION_SELECTION_CONDITIONS",
        ],
        "status": "EXECUTION_READINESS_PREPARATION_CONTRACT_FROZEN_REVIEW_REQUIRED_NO_PROTOTYPE_MIGRATION_CUTOVER_OR_AUTHORITY",
    }


def build_all() -> dict[Path, bytes]:
    schema_raw = canonical_json_bytes(build_schema_bundle())
    protocol_raw = canonical_json_bytes(build_protocol_bundle())
    packet_raw = canonical_json_bytes(build_packet())
    return {
        PACKET_PATH: packet_raw,
        PROTOCOL_BUNDLE_PATH: protocol_raw,
        SCHEMA_BUNDLE_PATH: schema_raw,
    }


def _forbidden_paths_absent() -> None:
    for relative in FORBIDDEN_PRODUCTION_PATHS:
        if (REPO_ROOT / relative).exists():
            raise ReadinessPacketError(f"forbidden production path exists: {relative}")


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


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build or verify the preparation-only registry sharding execution-readiness packet."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    _forbidden_paths_absent()
    artifacts = build_all()
    if args.check:
        for path, expected in artifacts.items():
            if not path.exists() or path.read_bytes() != expected:
                raise SystemExit(f"execution_readiness_packet: drift {path.relative_to(REPO_ROOT)}")
            print(
                "execution_readiness_packet: OK "
                f"{path.relative_to(REPO_ROOT).as_posix()} sha256={_sha256(expected)}"
            )
        return 0
    for path, raw in artifacts.items():
        _atomic_write(path, raw)
        print(
            "execution_readiness_packet: wrote "
            f"{path.relative_to(REPO_ROOT).as_posix()} sha256={_sha256(raw)}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
