from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from jsonschema.validators import validator_for

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "6e4d1e11b1953b9712588464b31c12047555189c"

PACKET_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "20260711_v0.json"
)
CONTRACT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v0.json"
)

V3_PACKET = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v3.json"
)
V3_PROTOCOL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v3.json"
)
V3_SCHEMAS = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3.json"
)
V3_REVIEW = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v3.json"
)
V1_GUARDRAIL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_"
    "20260711_v1.json"
)
V1_REVIEW = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_"
    "INDEPENDENT_REVIEW_20260711_v1.json"
)
CUSTODY_CONTRACT = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_LEGACY_BYTE_CUSTODY_CONTRACT_20260711_v1.json"
)
CONSUMER_MAP = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
REGISTRY = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_AUTHORITY = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
AUTHORITATIVE_SURFACES = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
READINESS_SOURCE = "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
REQUIREMENTS = "requirements.ci.lock"

EXPECTED: dict[str, tuple[str, str, int]] = {
    V3_PACKET: (
        "90037c92d74f4ab18be82863dd240065bc5ebd312e5b8647b52f1b3a549cb216",
        "9b257bee1abd276e586d0eaa557317b146420c6f",
        3393,
    ),
    V3_PROTOCOL: (
        "ad65ceb56d3b284b3a55e433afc13745c3c574c9f2e7bf0fe367172924ea08e2",
        "8d87fe5ddf9446296b71ace196d33b1c2e629ed5",
        187789,
    ),
    V3_SCHEMAS: (
        "86289bf922d60c3320f040779a6043cdb3f2acf3d5393ce7503ef9d3375f6cde",
        "eaf40d9fc8c6bd9364c2f016a19b3dc4f7b1d646",
        438862,
    ),
    V3_REVIEW: (
        "07353bc1c0d379518344aa16c25080fefb6dd9c1527cad4accb64216b15adae0",
        "46a1a5a230f30417cf5ee0ead962ebbdd1a243c9",
        3386,
    ),
    V1_GUARDRAIL: (
        "41994b0c1703d7f7f7ff7aeda217900a3136489f070ae55a88f2db10a13d12c0",
        "83069c2d254947176121dd9e9a4def0b9efd23b9",
        23432,
    ),
    V1_REVIEW: (
        "4b99d6d3801a8bbd2f918311116dfdfce8ef595f7c0e1b629bc3595820612dca",
        "90b0660e2c6108c5b8193c77a6c8400e9ebafb52",
        4572,
    ),
    CUSTODY_CONTRACT: (
        "bc35c992c9b9fd7dd9c2e84ed6d5b89463b3ce8eb13dc2f7c7d1c539b4d23ce9",
        "c2d47dd22e6c81180bae5d7e00e04b0121d12cf3",
        1918,
    ),
    CONSUMER_MAP: (
        "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
        "9f9846ba735813c5b2b18f7a0115d88230a36600",
        469583,
    ),
    REGISTRY: (
        "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
        "e6c5b3773dccd92fde9c0a8d486a56f993d6b235",
        52340650,
    ),
    MAINTENANCE_AUTHORITY: (
        "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
        "dca311d6abe38a872495c07f302d13ad886c0232",
        1768,
    ),
    AUTHORITATIVE_SURFACES: (
        "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
        "d46c5fb1966dcefc6b923776b7d94c4f5009b889",
        714575,
    ),
    READINESS_SOURCE: (
        "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
        "85711a7c8cb0bc6a1f77d85cf3873726a5d6aa22",
        79556,
    ),
    REQUIREMENTS: (
        "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
        "bcc393883b90739408ed14d53d57dd0b42d0c2bd",
        741,
    ),
}

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
PACKET_TARGET = "prepare_loop_control_registry_sharding_read_only_prototype_execution_packet_v0"
REVIEW_TARGET = "review_loop_control_registry_sharding_read_only_prototype_execution_packet_v0"
EXECUTION_TARGET = "execute_loop_control_registry_sharding_read_only_prototype_v0"
PACKET_REVIEW_PATH = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)
STAGE_A_REVIEW_PATH = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_STAGE_A_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)
STAGE_A_REVIEW_TARGET = "review_loop_control_registry_sharding_read_only_prototype_stage_a_v0"

HISTORICAL_GATES = [
    ("v0_preparation", "bf8c12918675d77c27c0eadde009134fc572c281"),
    ("v0_corrected_pre_review_boundary", "a0d44da40922d6547f02241174fa640edb3f9fa8"),
    ("v0_review", "be985ab12d1947b188d773aaf5d9f64de097770e"),
    ("v1_preparation", "e2af09bbb4355604eee4566707afd3407ed6c4b9"),
    ("v1_review", "5f6672b13f1bff7653cb7caa3fc5b4e80276fc2a"),
    ("v2_preparation", "20a57192305cc794397fdcef06f54cab30c37205"),
    ("v2_review", "ee287de3db44bd4fe5a1c9c9952c07be9d2e9248"),
    ("v3_preparation", "f9051af27988dd745bf39d28ae4d610973d5a029"),
    ("v3_review", SOURCE_COMMIT),
]

FORBIDDEN_TRANSITION_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/scratch/loop_control_registry_v1_prototype",
]

CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION = [
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet.py",
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet_v1.py",
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet_v2.py",
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet_v3.py",
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet_v3_independent_review.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet_v1.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet_v2.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet_v3.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet_v3_independent_review.py",
]

HISTORICAL_CHECK_BOUNDARIES = {
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[0]: "a0d44da40922d6547f02241174fa640edb3f9fa8",
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[5]: "a0d44da40922d6547f02241174fa640edb3f9fa8",
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[1]: "e2af09bbb4355604eee4566707afd3407ed6c4b9",
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[6]: "e2af09bbb4355604eee4566707afd3407ed6c4b9",
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[2]: "20a57192305cc794397fdcef06f54cab30c37205",
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[7]: "20a57192305cc794397fdcef06f54cab30c37205",
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[3]: "f9051af27988dd745bf39d28ae4d610973d5a029",
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[8]: "f9051af27988dd745bf39d28ae4d610973d5a029",
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[4]: SOURCE_COMMIT,
    CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION[9]: SOURCE_COMMIT,
}

RUNTIME_ERROR_PRECEDENCE = [
    "V1-E-RUNTIME-SCHEMA",
    "V1-E-RUNTIME-FORMAT",
    "V1-E-TRUST-ANCHOR-EXTERNAL-BINDING",
    "V1-E-PREFLIGHT-GIT-BINDING",
    "V1-E-IMPLEMENTATION-TREE",
    "V1-E-CONSUMER-INVENTORY-DELTA",
    "V1-E-ARTIFACT-KIND-PATH",
    "V1-E-ARTIFACT-INVENTORY",
    "V1-E-CANDIDATE-TREE",
    "V1-E-WRITER-PROBE",
    "V1-E-ROLLBACK-INVENTORY",
    "V1-E-RESULT-ENVELOPE",
    "V1-E-STAGE-A-CONTROL-RESULT",
    "V1-E-STAGE-A-BASELINE",
    "V1-E-STAGE-A-ACCEPTANCE",
    "V1-E-STAGE-B-ACCEPTANCE",
    "V1-E-RUN-MANIFEST",
    "V1-E-RUNTIME-CROSS-DOCUMENT",
]

RUNTIME_NEGATIVE_CONTROLS = [
    ("RUNTIME-NC-001", "unknown_schema_field", "V1-E-RUNTIME-SCHEMA"),
    ("RUNTIME-NC-002", "invalid_date_time", "V1-E-RUNTIME-FORMAT"),
    ("RUNTIME-NC-003", "candidate_rebound_review_anchor", "V1-E-TRUST-ANCHOR-EXTERNAL-BINDING"),
    ("RUNTIME-NC-004", "packet_review_not_implementation_ancestor", "V1-E-PREFLIGHT-GIT-BINDING"),
    ("RUNTIME-NC-005", "artifact_kind_path_relabel", "V1-E-ARTIFACT-KIND-PATH"),
    ("RUNTIME-NC-006", "duplicate_artifact_path_with_changed_hash", "V1-E-ARTIFACT-INVENTORY"),
    ("RUNTIME-NC-007", "rebound_incomplete_candidate_tree", "V1-E-CANDIDATE-TREE"),
    ("RUNTIME-NC-008", "writer_probe_outside_run_root", "V1-E-WRITER-PROBE"),
    ("RUNTIME-NC-009", "rollback_inventory_outside_run_root", "V1-E-ROLLBACK-INVENTORY"),
    ("RUNTIME-NC-010", "noncanonical_base64_or_payload_hash", "V1-E-RESULT-ENVELOPE"),
    ("RUNTIME-NC-011", "stage_a_missing_or_reordered_control", "V1-E-STAGE-A-CONTROL-RESULT"),
    ("RUNTIME-NC-012", "stage_a_positive_baseline_did_not_pass", "V1-E-STAGE-A-BASELINE"),
    ("RUNTIME-NC-013", "stage_a_before_after_candidate_hash_mismatch", "V1-E-STAGE-A-BASELINE"),
    ("RUNTIME-NC-014", "candidate_supplied_stage_a_acceptance", "V1-E-STAGE-A-ACCEPTANCE"),
    ("RUNTIME-NC-015", "stage_b_without_reviewed_stage_a", "V1-E-STAGE-B-ACCEPTANCE"),
    ("RUNTIME-NC-016", "cross_document_run_id_or_identity_mismatch", "V1-E-RUNTIME-CROSS-DOCUMENT"),
    ("RUNTIME-NC-017", "rebound_implementation_tree_root", "V1-E-IMPLEMENTATION-TREE"),
    ("RUNTIME-NC-018", "rebound_consumer_inventory_delta_root", "V1-E-CONSUMER-INVENTORY-DELTA"),
]


class PrototypePreparationError(ValueError):
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


def _git_blob(commit: str, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise PrototypePreparationError(f"missing reviewed blob: {commit}:{relative}")
    return result.stdout


def _git_oid(commit: str, relative: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _path_absent(commit: str, relative: str) -> bool:
    return (
        subprocess.run(
            ["git", "cat-file", "-e", f"{commit}:{relative}"],
            cwd=REPO_ROOT,
            capture_output=True,
            check=False,
        ).returncode
        != 0
    )


def _strict_json(raw: bytes) -> Any:
    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise PrototypePreparationError(f"duplicate JSON key: {key}")
            output[key] = value
        return output

    def reject_constant(value: str) -> Any:
        raise PrototypePreparationError(f"nonfinite JSON constant: {value}")

    return json.loads(raw, object_pairs_hook=pairs_hook, parse_constant=reject_constant)


def _closed(properties: dict[str, Any], required: list[str] | None = None) -> dict[str, Any]:
    return {
        "additionalProperties": False,
        "properties": properties,
        "required": list(properties) if required is None else required,
        "type": "object",
    }


def _identity_schema(path_profile: dict[str, Any]) -> dict[str, Any]:
    return _closed(
        {
            "path": deepcopy(path_profile),
            "sha256": {"pattern": "^[0-9a-f]{64}$", "type": "string"},
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )


def _runtime_schemas(
    path_profiles: dict[str, Any], stage_a_rows: list[dict[str, Any]], control_error_map: dict[str, str]
) -> dict[str, Any]:
    repo_path = {
        "maxLength": 240,
        "minLength": 1,
        "pattern": path_profiles["REPOSITORY_RELPATH"]["pattern"],
        "type": "string",
    }
    prototype_path = {
        "maxLength": 240,
        "minLength": 1,
        "pattern": path_profiles["PROTOTYPE_ARTIFACT_RELPATH"]["pattern"],
        "type": "string",
    }
    run_id = {"pattern": path_profiles["RUN_ID"]["pattern"], "type": "string"}
    run_root = {
        "pattern": (
            "^formal/scratch/loop_control_registry_v1_prototype/"
            "[A-Za-z0-9][A-Za-z0-9_-]{0,63}$"
        ),
        "type": "string",
    }
    sha = {"pattern": "^[0-9a-f]{64}$", "type": "string"}
    commit = {"pattern": "^[0-9a-f]{40}$", "type": "string"}
    utc_timestamp = {
        "format": "date-time",
        "pattern": (
            "^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}"
            "(?:[.][0-9]{1,6})?Z$"
        ),
        "type": "string",
    }
    identity = _identity_schema(prototype_path)

    reviewed_anchors = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1",
                "type": "string",
            },
            "v3_acceptance_commit": {"const": SOURCE_COMMIT, "type": "string"},
            "accepted_v3_review": _closed(
                {
                    "path": {"const": V3_REVIEW, "type": "string"},
                    "sha256": {"const": EXPECTED[V3_REVIEW][0], "type": "string"},
                    "reviewed_preparation_commit": {
                        "const": "f9051af27988dd745bf39d28ae4d610973d5a029",
                        "type": "string",
                    },
                }
            ),
            "v3_contract": _closed(
                {
                    "packet_sha256": {"const": EXPECTED[V3_PACKET][0], "type": "string"},
                    "protocol_sha256": {"const": EXPECTED[V3_PROTOCOL][0], "type": "string"},
                    "schema_bundle_sha256": {"const": EXPECTED[V3_SCHEMAS][0], "type": "string"},
                }
            ),
            "external_v1": _closed(
                {
                    "source_commit": {
                        "const": "6aba59d8d399b331db010f1f5f857075b9100b7f",
                        "type": "string",
                    },
                    "guardrail_sha256": {"const": EXPECTED[V1_GUARDRAIL][0], "type": "string"},
                    "review_sha256": {"const": EXPECTED[V1_REVIEW][0], "type": "string"},
                }
            ),
            "source_registry": _closed(
                {
                    "source_commit": {
                        "const": "f9168ab5f566fb2019b9e76e68ff3e60e5c0dc52",
                        "type": "string",
                    },
                    "path": {"const": REGISTRY, "type": "string"},
                    "git_blob": {"const": EXPECTED[REGISTRY][1], "type": "string"},
                    "sha256": {"const": EXPECTED[REGISTRY][0], "type": "string"},
                    "size_bytes": {"const": EXPECTED[REGISTRY][2], "type": "integer"},
                }
            ),
            "authority_commitment_sha256": {
                "const": "fd4348411236648d6216900eced59524b87c561bfa0d36186cf4c4d19a2e6b34",
                "type": "string",
            },
            "requirements_lock_sha256": {"const": EXPECTED[REQUIREMENTS][0], "type": "string"},
            "prototype_execution_authorization": _closed(
                {
                    "packet_path": {"const": PACKET_PATH.relative_to(REPO_ROOT).as_posix(), "type": "string"},
                    "packet_sha256": deepcopy(sha),
                    "reviewed_packet_commit": deepcopy(commit),
                    "independent_review_path": {"const": PACKET_REVIEW_PATH, "type": "string"},
                    "independent_review_sha256": deepcopy(sha),
                    "authorization_review_commit": deepcopy(commit),
                    "bounded_stage_a_authorized": {"const": True, "type": "boolean"},
                    "stage_b_authorized": {"const": False, "type": "boolean"},
                    "anchor_source": {
                        "const": "GIT_COMMIT_VERIFIED_INDEPENDENT_REVIEW",
                        "type": "string",
                    },
                }
            ),
            "candidate_supplied_values_authoritative": {"const": False, "type": "boolean"},
        }
    )

    inventory_item = _closed(
        {
            "artifact_kind": {
                "enum": [
                    "COMPATIBILITY_RECONSTRUCTION",
                    "CONSUMER_SOURCE_MAP",
                    "CONTROL_HARNESS_REPORT",
                    "CURRENT_PROJECTION",
                    "CUSTODY_MANIFEST",
                    "CUSTODY_PAYLOAD",
                    "EXECUTION_PREFLIGHT",
                    "HISTORY_INDEX",
                    "HISTORY_SHARD",
                    "RECONSTRUCTION_RESULT",
                    "REVIEWED_TRUST_ANCHORS",
                    "ROLLBACK_INVENTORY",
                    "RUNTIME_RUN_MANIFEST",
                    "RUNTIME_SHADOW_TRACE",
                    "RUNTIME_SHADOW_TRACE_MANIFEST",
                    "STAGE_A_PRECUTOVER_REPORT",
                    "STAGE_B_FULL_HARNESS_RESULT",
                    "VALIDATION_REPORT",
                    "WRITER_PROBE",
                ],
                "type": "string",
            },
            "candidate_payload": {"type": "boolean"},
            "path": deepcopy(prototype_path),
            "sha256": deepcopy(sha),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )
    artifact_source = _closed(
        {
            "schema_id": {"const": "LOOP_CONTROL_ARTIFACT_SOURCE_MANIFEST_v1", "type": "string"},
            "run_id": deepcopy(run_id),
            "source_commit": deepcopy(commit),
            "implementation_commit": deepcopy(commit),
            "run_root_repo_relative": deepcopy(run_root),
            "candidate_tree_sha256": deepcopy(sha),
            "inventory_sha256": deepcopy(sha),
            "inventory_algorithm_id": {
                "const": "LOOP_CONTROL_RUN_ARTIFACT_INVENTORY_ROOT_v1",
                "type": "string",
            },
            "candidate_tree_algorithm_id": {
                "const": "LOOP_CONTROL_CANDIDATE_PAYLOAD_TREE_ROOT_v1",
                "type": "string",
            },
            "candidate_payload_artifact_count": {"minimum": 1, "type": "integer"},
            "evidence_artifact_count": {"minimum": 0, "type": "integer"},
            "artifacts": {"items": inventory_item, "minItems": 1, "type": "array", "uniqueItems": True},
            "immutable": {"const": True, "type": "boolean"},
        }
    )
    write_item = {
        "oneOf": [
            _closed(
                {
                    "path": deepcopy(repo_path),
                    "path_context": {"const": "REPOSITORY_RELPATH", "type": "string"},
                }
            ),
            _closed(
                {
                    "path": deepcopy(prototype_path),
                    "path_context": {
                        "const": "PROTOTYPE_ARTIFACT_RELPATH",
                        "type": "string",
                    },
                }
            ),
        ]
    }
    writer_probe = _closed(
        {
            "schema_id": {"const": "LOOP_CONTROL_WRITER_PROBE_v1", "type": "string"},
            "run_id": deepcopy(run_id),
            "attempted_writes": {"items": write_item, "type": "array", "uniqueItems": True},
            "writes_outside_run_root": {"const": 0, "type": "integer"},
            "history_mutation_performed": {"const": False, "type": "boolean"},
            "new_api_write_performed": {"const": False, "type": "boolean"},
            "source_registry_sha256_before": {"const": EXPECTED[REGISTRY][0], "type": "string"},
            "source_registry_sha256_after": {"const": EXPECTED[REGISTRY][0], "type": "string"},
        }
    )
    rollback_inventory = _closed(
        {
            "schema_id": {"const": "LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v1", "type": "string"},
            "run_id": deepcopy(run_id),
            "run_root_repo_relative": deepcopy(run_root),
            "pre_run_inventory_sha256": deepcopy(sha),
            "created_paths": {"items": deepcopy(prototype_path), "type": "array", "uniqueItems": True},
            "created_paths_root_sha256": deepcopy(sha),
            "outside_run_root_created_path_count": {"const": 0, "type": "integer"},
            "rollback_eligible": {"type": "boolean"},
        }
    )
    value_envelope = _closed(
        {
            "result_kind": {"const": "VALUE", "type": "string"},
            "type_tag": {"minLength": 1, "type": "string"},
            "canonical_json_utf8_base64": {
                "pattern": "^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$",
                "type": "string",
            },
            "payload_sha256": deepcopy(sha),
        }
    )
    exception_envelope = _closed(
        {
            "result_kind": {"const": "EXCEPTION", "type": "string"},
            "exception_type": {"minLength": 1, "type": "string"},
            "message_utf8_base64": {
                "pattern": "^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$",
                "type": "string",
            },
            "payload_sha256": deepcopy(sha),
        }
    )
    result_envelope = {"oneOf": [value_envelope, exception_envelope]}

    stage_a_control_result_schemas = []
    for row in stage_a_rows:
        control_id = row["control_id"]
        expected_error = control_error_map[control_id]
        exact_error_array = {
            "items": False,
            "maxItems": 1,
            "minItems": 1,
            "prefixItems": [{"const": expected_error, "type": "string"}],
            "type": "array",
        }
        stage_a_control_result_schemas.append(
            _closed(
                {
                    "control_id": {"const": control_id, "type": "string"},
                    "validator_profile": {"const": row["validator_profile"], "type": "string"},
                    "expected_decision": {"const": "REJECT", "type": "string"},
                    "observed_decision": {"const": "REJECT", "type": "string"},
                    "expected_error_codes": deepcopy(exact_error_array),
                    "observed_error_codes": deepcopy(exact_error_array),
                    "baseline_candidate_sha256_before": deepcopy(sha),
                    "baseline_candidate_sha256_after": deepcopy(sha),
                    "positive_baseline_passed_before_mutation": {
                        "const": True,
                        "type": "boolean",
                    },
                    "baseline_recreated_for_control": {"const": True, "type": "boolean"},
                    "subsequent_controls_received_unmodified_baseline": {
                        "const": True,
                        "type": "boolean",
                    },
                    "passed": {"const": True, "type": "boolean"},
                }
            )
        )
    exact_stage_a_results = {
        "items": False,
        "maxItems": len(stage_a_control_result_schemas),
        "minItems": len(stage_a_control_result_schemas),
        "prefixItems": stage_a_control_result_schemas,
        "type": "array",
    }
    runtime_contract_result_schemas = [
        _closed(
            {
                "control_id": {"const": control_id, "type": "string"},
                "mutation": {"const": mutation, "type": "string"},
                "expected_error": {"const": error, "type": "string"},
                "observed_error": {"const": error, "type": "string"},
                "fresh_baseline": {"const": True, "type": "boolean"},
                "subsequent_controls_unmodified": {"const": True, "type": "boolean"},
                "passed": {"const": True, "type": "boolean"},
            }
        )
        for control_id, mutation, error in RUNTIME_NEGATIVE_CONTROLS
    ]
    exact_runtime_contract_results = {
        "items": False,
        "maxItems": len(runtime_contract_result_schemas),
        "minItems": len(runtime_contract_result_schemas),
        "prefixItems": runtime_contract_result_schemas,
        "type": "array",
    }
    stage_a_profile_roots = {}
    for profile in [
        "PROTOTYPE_INTEGRITY",
        "WRITE_SAFETY",
        "SHADOW_PARITY",
        "CUTOVER_ELIGIBILITY",
    ]:
        profile_ids = [
            row["control_id"] for row in stage_a_rows if row["validator_profile"] == profile
        ]
        stage_a_profile_roots[profile] = _sha256("\n".join(profile_ids).encode("utf-8"))
    stage_a = _closed(
        {
            "schema_id": {"const": "LOOP_CONTROL_STAGE_A_PRECUTOVER_REPORT_v1", "type": "string"},
            "run_id": deepcopy(run_id),
            "candidate_tree_sha256": deepcopy(sha),
            "primary_controls_passed": {"const": 51, "type": "integer"},
            "readiness_controls_passed": {"const": 7, "type": "integer"},
            "distinct_controls_passed": {"const": 58, "type": "integer"},
            "runtime_contract_controls_passed": {
                "const": len(RUNTIME_NEGATIVE_CONTROLS),
                "type": "integer",
            },
            "total_controls_passed": {
                "const": 58 + len(RUNTIME_NEGATIVE_CONTROLS),
                "type": "integer",
            },
            "cutover_controls_executed": {"const": False, "type": "boolean"},
            "final_harness_report_emitted": {"const": False, "type": "boolean"},
            "control_results": exact_stage_a_results,
            "control_results_root_sha256": deepcopy(sha),
            "runtime_contract_control_results": exact_runtime_contract_results,
            "runtime_contract_results_root_sha256": deepcopy(sha),
            "stage_a_profile_control_roots": _closed(
                {
                    profile: {"const": root, "type": "string"}
                    for profile, root in stage_a_profile_roots.items()
                }
            ),
            "baseline_isolation_verified": {"const": True, "type": "boolean"},
            "shadow_manifest": deepcopy(identity),
            "custody_manifest": deepcopy(identity),
            "reconstruction_result": deepcopy(identity),
            "status": {"const": "PRE_CUTOVER_EVIDENCE_COMPLETE_REVIEW_REQUIRED", "type": "string"},
        }
    )
    stage_a_binding = _closed(
        {
            "schema_id": {"const": "LOOP_CONTROL_STAGE_A_ACCEPTANCE_BINDING_v1", "type": "string"},
            "review_commit": deepcopy(commit),
            "review_path": {"const": STAGE_A_REVIEW_PATH, "type": "string"},
            "review_sha256": deepcopy(sha),
            "review_schema_id": {
                "const": "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_STAGE_A_INDEPENDENT_REVIEW_20260711_v0",
                "type": "string",
            },
            "review_target": {"const": STAGE_A_REVIEW_TARGET, "type": "string"},
            "implementation_commit": deepcopy(commit),
            "candidate_tree_sha256": deepcopy(sha),
            "stage_a_report_path": deepcopy(prototype_path),
            "stage_a_report_sha256": deepcopy(sha),
            "shadow_manifest_path": deepcopy(prototype_path),
            "shadow_manifest_sha256": deepcopy(sha),
            "shadow_run_id": deepcopy(run_id),
            "accepted": {"const": True, "type": "boolean"},
            "stage_b_full_harness_authorized": {"const": False, "type": "boolean"},
            "stage_b_successor_packet_required": {"const": True, "type": "boolean"},
            "migration_execution_authorized": {"const": False, "type": "boolean"},
            "cutover_authorized": {"const": False, "type": "boolean"},
        }
    )
    stage_b = _closed(
        {
            "schema_id": {"const": "LOOP_CONTROL_STAGE_B_FULL_HARNESS_RESULT_v1", "type": "string"},
            "run_id": deepcopy(run_id),
            "candidate_tree_sha256": deepcopy(sha),
            "accepted_stage_a": stage_a_binding,
            "primary_controls_passed": {"const": 52, "type": "integer"},
            "readiness_controls_passed": {"const": 8, "type": "integer"},
            "distinct_controls_passed": {"const": 60, "type": "integer"},
            "runtime_contract_controls_passed": {
                "const": len(RUNTIME_NEGATIVE_CONTROLS),
                "type": "integer",
            },
            "total_controls_passed": {
                "const": 60 + len(RUNTIME_NEGATIVE_CONTROLS),
                "type": "integer",
            },
            "effective_profile_invocations_passed": {"const": 199, "type": "integer"},
            "control_harness_report": deepcopy(identity),
            "migration_execution_authorized": {"const": False, "type": "boolean"},
            "cutover_authorized": {"const": False, "type": "boolean"},
            "status": {"const": "FULL_READ_ONLY_HARNESS_COMPLETE_REVIEW_REQUIRED", "type": "string"},
        }
    )
    runtime_run_manifest = _closed(
        {
            "schema_id": {"const": "LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v1", "type": "string"},
            "run_id": deepcopy(run_id),
            "stage": {"enum": ["STAGE_A", "STAGE_B"], "type": "string"},
            "reviewed_trust_anchors_sha256": deepcopy(sha),
            "artifact_source_manifest": deepcopy(identity),
            "writer_probe": deepcopy(identity),
            "rollback_inventory": deepcopy(identity),
            "started_at_utc": deepcopy(utc_timestamp),
            "finished_at_utc": deepcopy(utc_timestamp),
            "timed_out": {"const": False, "type": "boolean"},
            "pre_run_detached_checkout_clean": {"const": True, "type": "boolean"},
            "post_run_only_allowlisted_run_root_changes": {"const": True, "type": "boolean"},
            "post_run_protected_files_unchanged": {"const": True, "type": "boolean"},
        }
    )
    nullable_sha = {"oneOf": [deepcopy(sha), {"type": "null"}]}
    nullable_consumer_id = {
        "oneOf": [
            {"pattern": "^lcc1:[0-9a-f]{64}$", "type": "string"},
            {"type": "null"},
        ]
    }
    consumer_inventory_row = _closed(
        {
            "path": deepcopy(repo_path),
            "delta_class": {
                "enum": ["UNCHANGED", "CHANGED", "NEW", "RETIRED"],
                "type": "string",
            },
            "baseline_consumer_id": deepcopy(nullable_consumer_id),
            "current_consumer_id": deepcopy(nullable_consumer_id),
            "baseline_source_sha256": deepcopy(nullable_sha),
            "current_source_sha256": deepcopy(nullable_sha),
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
            "access_operation": {
                "enum": [
                    "DYNAMIC_READER",
                    "PATH_REFERENCE_ONLY",
                    "STATIC_READER_CANDIDATE",
                    "WRITER_AND_READER",
                ],
                "type": "string",
            },
            "disposition": {
                "enum": [
                    "RUNTIME_TRACE_REQUIRED",
                    "PROVED_NONRUNTIME",
                    "RETIRED_WITH_JUSTIFICATION",
                ],
                "type": "string",
            },
            "disposition_reason": {"minLength": 1, "type": "string"},
        }
    )
    execution_preflight = _closed(
        {
            "schema_id": {"const": "LOOP_CONTROL_READ_ONLY_PROTOTYPE_EXECUTION_PREFLIGHT_v1", "type": "string"},
            "packet_review_path": {"const": PACKET_REVIEW_PATH, "type": "string"},
            "packet_review_sha256": deepcopy(sha),
            "authorization_review_commit": deepcopy(commit),
            "authorization_review_is_ancestor_of_implementation": {"const": True, "type": "boolean"},
            "implementation_commit": deepcopy(commit),
            "implementation_tree_sha256": deepcopy(sha),
            "head_commit": deepcopy(commit),
            "main_commit": deepcopy(commit),
            "origin_main_commit": deepcopy(commit),
            "main_equals_origin_main": {"const": True, "type": "boolean"},
            "head_main_origin_equal_implementation_commit": {"const": True, "type": "boolean"},
            "worktree_clean": {"const": True, "type": "boolean"},
            "v3_acceptance_commit": {"const": SOURCE_COMMIT, "type": "string"},
            "source_registry_sha256": {"const": EXPECTED[REGISTRY][0], "type": "string"},
            "historical_record_count": {"const": 4691, "type": "integer"},
            "baseline_classified_consumer_path_count": {"const": 496, "type": "integer"},
            "baseline_consumer_map_sha256": {"const": EXPECTED[CONSUMER_MAP][0], "type": "string"},
            "current_consumer_path_count": {"minimum": 496, "type": "integer"},
            "consumer_inventory_delta_root_sha256": deepcopy(sha),
            "consumer_inventory_rows": {
                "items": consumer_inventory_row,
                "minItems": 496,
                "type": "array",
                "uniqueItems": True,
            },
            "all_baseline_and_current_consumer_rows_dispositioned": {
                "const": True,
                "type": "boolean",
            },
            "protected_bindings_reverified": {"const": True, "type": "boolean"},
        }
    )

    schemas = {
        "reviewed_trust_anchors": reviewed_anchors,
        "artifact_source_manifest": artifact_source,
        "writer_probe": writer_probe,
        "run_rollback_inventory": rollback_inventory,
        "typed_result_envelope": result_envelope,
        "stage_a_precutover_report": stage_a,
        "stage_a_acceptance_binding": stage_a_binding,
        "stage_b_full_harness_result": stage_b,
        "runtime_run_manifest": runtime_run_manifest,
        "execution_preflight": execution_preflight,
    }
    for name, schema in schemas.items():
        schema["$schema"] = "https://json-schema.org/draft/2020-12/schema"
        schema["$id"] = f"https://toe.local/schema/prototype-execution-v0/{name.replace('_', '-')}.schema.json"
        validator_for(schema).check_schema(schema)
    return schemas


def _inputs() -> dict[str, Any]:
    bindings: dict[str, Any] = {}
    parsed: dict[str, Any] = {}
    for path, (sha256, oid, size) in EXPECTED.items():
        raw = _git_blob(SOURCE_COMMIT, path)
        if _sha256(raw) != sha256 or len(raw) != size or _git_oid(SOURCE_COMMIT, path) != oid:
            raise PrototypePreparationError(f"source binding drift: {path}")
        bindings[path] = {
            "git_blob": oid,
            "path": path,
            "sha256": sha256,
            "size_bytes": size,
        }
        if path.endswith(".json"):
            parsed[path] = _strict_json(raw)

    packet = parsed[V3_PACKET]
    protocol = parsed[V3_PROTOCOL]
    schemas = parsed[V3_SCHEMAS]
    review = parsed[V3_REVIEW]
    guardrail = parsed[V1_GUARDRAIL]
    maintenance = parsed[MAINTENANCE_AUTHORITY]
    consumer_map = parsed[CONSUMER_MAP]
    if review["authorization"]["corrective_v3_preparation_accepted"] is not True:
        raise PrototypePreparationError("accepted v3 review drift")
    if review["authorization"]["registry_migration_execution_readiness_accepted"] is not False:
        raise PrototypePreparationError("v3 review unexpectedly authorizes migration readiness")
    if any(packet["boundary"].values()):
        raise PrototypePreparationError("v3 preparation boundary drift")
    if packet["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise PrototypePreparationError("scientific target drift")
    if packet["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise PrototypePreparationError("maintenance target drift")
    if maintenance["scientific_authority"]["current_target"] != SCIENTIFIC_TARGET:
        raise PrototypePreparationError("maintenance mirror scientific target drift")
    if maintenance["current_maintenance_target"] != MAINTENANCE_TARGET:
        raise PrototypePreparationError("maintenance authority drift")
    if protocol["typed_control_harness"]["control_count"] != 52:
        raise PrototypePreparationError("primary control count drift")
    if protocol["typed_control_harness"]["readiness_regression_control_count"] != 8:
        raise PrototypePreparationError("readiness control count drift")
    if schemas["schema_count"] != 10 or guardrail["record_accounting"]["total_record_count"] != 4691:
        raise PrototypePreparationError("schema or record scale drift")
    if consumer_map["consumer_count"] != 496 or len(consumer_map["consumers"]) != 496:
        raise PrototypePreparationError("classified consumer inventory drift")
    return {
        "bindings": bindings,
        "packet": packet,
        "protocol": protocol,
        "schemas": schemas,
        "review": review,
        "guardrail": guardrail,
        "custody": parsed[CUSTODY_CONTRACT],
    }


def _historical_absence_transition() -> dict[str, Any]:
    gates = []
    for name, commit in HISTORICAL_GATES:
        absent = [path for path in FORBIDDEN_TRANSITION_PATHS if _path_absent(commit, path)]
        if len(absent) != len(FORBIDDEN_TRANSITION_PATHS):
            raise PrototypePreparationError(f"historical production-path presence at {name}")
        gates.append(
            {
                "all_forbidden_paths_absent": True,
                "commit": commit,
                "forbidden_path_count": len(absent),
                "gate": name,
            }
        )
    affected_source_bindings = {}
    for relative in CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION:
        raw = _git_blob(SOURCE_COMMIT, relative)
        affected_source_bindings[relative] = {
            "git_blob": _git_oid(SOURCE_COMMIT, relative),
            "sha256": _sha256(raw),
            "size_bytes": len(raw),
        }
    return {
        "affected_check_source_bindings": affected_source_bindings,
        "forbidden_paths": FORBIDDEN_TRANSITION_PATHS,
        "gate_count": len(gates),
        "gates": gates,
        "transition_claim": (
            "V0_THROUGH_ACCEPTED_V3_ARE_PREPARATION_OR_REVIEW_ONLY_AND_CREATED_NO_"
            "PRODUCTION_LAYOUT_API_VALIDATOR_CUSTODY_OR_PROTOTYPE_ROOT"
        ),
    }


def build_contract() -> dict[str, Any]:
    source = _inputs()
    protocol = source["protocol"]
    schemas = source["schemas"]
    guardrail = source["guardrail"]
    controls = deepcopy(protocol["typed_control_harness"]["controls"])
    readiness = deepcopy(protocol["typed_control_harness"]["readiness_regressions"])
    primary_stage_a = [row["control_id"] for row in controls if row["control_id"] != "REGISTRY-V1-NC-044"]
    readiness_stage_a = [row["control_id"] for row in readiness if row["control_id"] != "REGISTRY-READINESS-V1-RC-001"]
    if len(primary_stage_a) != 51 or len(readiness_stage_a) != 7:
        raise PrototypePreparationError("staged control partition drift")
    stage_a_rows = [
        row for row in controls if row["control_id"] in set(primary_stage_a)
    ] + [row for row in readiness if row["control_id"] in set(readiness_stage_a)]
    runtime_schemas = _runtime_schemas(
        schemas["path_profiles"], stage_a_rows, protocol["control_error_map"]
    )
    runtime_artifact_paths = deepcopy(
        protocol["prototype_paths"]["artifact_paths_relative_to_run_root"]
    )
    runtime_artifact_paths.update(
        {
            "reviewed_trust_anchors": "authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json",
            "artifact_source_manifest": "manifests/LOOP_CONTROL_ARTIFACT_SOURCE_MANIFEST_v1.json",
            "writer_probe": "validation/LOOP_CONTROL_WRITER_PROBE_v1.json",
            "run_rollback_inventory": "manifests/LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v1.json",
            "stage_a_precutover_report": "validation/LOOP_CONTROL_STAGE_A_PRECUTOVER_REPORT_v1.json",
            "stage_b_full_harness_result": "validation/LOOP_CONTROL_STAGE_B_FULL_HARNESS_RESULT_v1.json",
            "runtime_run_manifest": "manifests/LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v1.json",
            "execution_preflight": "manifests/LOOP_CONTROL_EXECUTION_PREFLIGHT_v1.json",
        }
    )
    runtime_artifact_kind_by_key = {
        "compatibility_reconstruction": "COMPATIBILITY_RECONSTRUCTION",
        "consumer_source_map": "CONSUMER_SOURCE_MAP",
        "control_harness_report": "CONTROL_HARNESS_REPORT",
        "current_projection": "CURRENT_PROJECTION",
        "custody_manifest": "CUSTODY_MANIFEST",
        "custody_payload": "CUSTODY_PAYLOAD",
        "history_index": "HISTORY_INDEX",
        "reconstruction_result": "RECONSTRUCTION_RESULT",
        "runtime_shadow_trace": "RUNTIME_SHADOW_TRACE",
        "runtime_shadow_trace_manifest": "RUNTIME_SHADOW_TRACE_MANIFEST",
        "validation_report": "VALIDATION_REPORT",
        "reviewed_trust_anchors": "REVIEWED_TRUST_ANCHORS",
        "artifact_source_manifest": "ARTIFACT_SOURCE_MANIFEST",
        "writer_probe": "WRITER_PROBE",
        "run_rollback_inventory": "ROLLBACK_INVENTORY",
        "stage_a_precutover_report": "STAGE_A_PRECUTOVER_REPORT",
        "stage_b_full_harness_result": "STAGE_B_FULL_HARNESS_RESULT",
        "runtime_run_manifest": "RUNTIME_RUN_MANIFEST",
        "execution_preflight": "EXECUTION_PREFLIGHT",
    }
    runtime_schema_artifact_mapping = {
        "reviewed_trust_anchors": {
            "disposition": "STANDALONE",
            "path": runtime_artifact_paths["reviewed_trust_anchors"],
        },
        "artifact_source_manifest": {
            "disposition": "STANDALONE",
            "path": runtime_artifact_paths["artifact_source_manifest"],
        },
        "writer_probe": {
            "disposition": "STANDALONE",
            "path": runtime_artifact_paths["writer_probe"],
        },
        "run_rollback_inventory": {
            "disposition": "STANDALONE",
            "path": runtime_artifact_paths["run_rollback_inventory"],
        },
        "typed_result_envelope": {
            "disposition": "IN_MEMORY_ONLY",
            "feeds_artifact": "runtime_shadow_trace",
            "feeds_fields": ["legacy_result_sha256", "candidate_result_sha256"],
        },
        "stage_a_precutover_report": {
            "disposition": "STANDALONE",
            "path": runtime_artifact_paths["stage_a_precutover_report"],
        },
        "stage_a_acceptance_binding": {
            "disposition": "DEFERRED_SUCCESSOR_ONLY",
            "external_path": STAGE_A_REVIEW_PATH,
            "external_source_required": "INDEPENDENT_STAGE_A_REVIEW_IN_GIT",
        },
        "stage_b_full_harness_result": {
            "disposition": "DEFERRED_SUCCESSOR_ONLY",
            "path": runtime_artifact_paths["stage_b_full_harness_result"],
        },
        "runtime_run_manifest": {
            "disposition": "STANDALONE",
            "path": runtime_artifact_paths["runtime_run_manifest"],
        },
        "execution_preflight": {
            "disposition": "STANDALONE",
            "path": runtime_artifact_paths["execution_preflight"],
        },
    }
    if set(runtime_schema_artifact_mapping) != set(runtime_schemas):
        raise PrototypePreparationError("runtime schema artifact mapping is not total")
    standalone_runtime_paths = [
        row["path"]
        for row in runtime_schema_artifact_mapping.values()
        if row["disposition"] == "STANDALONE"
    ]
    if len(standalone_runtime_paths) != len(set(standalone_runtime_paths)):
        raise PrototypePreparationError("standalone runtime schema paths are not injective")
    if not set(standalone_runtime_paths).issubset(set(runtime_artifact_paths.values())):
        raise PrototypePreparationError("standalone runtime schema path is not allowlisted")

    canonical_api = {
        "canonical_anchor_type": "ReviewedTrustAnchors",
        "canonical_stage_a_acceptance_type": "ReviewedStageAAcceptance",
        "forbidden_unresolved_alias": "RegistryTrustAnchors",
        "external_git_verified_loaders": [
            "load_reviewed_trust_anchors(review_commit: str, expected_sha256: str) -> ReviewedTrustAnchors",
            "load_reviewed_stage_a_acceptance(review_commit: str, expected_sha256: str) -> ReviewedStageAAcceptance",
        ],
        "fixed_packet_review_path": PACKET_REVIEW_PATH,
        "fixed_stage_a_review_path": STAGE_A_REVIEW_PATH,
        "fixed_stage_a_review_target": STAGE_A_REVIEW_TARGET,
        "public_profile_entrypoints": [
            "validate_prototype_integrity(candidate_root: Path, anchors: ReviewedTrustAnchors) -> ValidationReport",
            "validate_write_safety(candidate_root: Path, anchors: ReviewedTrustAnchors, writer_probe: WriterProbe) -> ValidationReport",
            "validate_shadow_parity(candidate_root: Path, anchors: ReviewedTrustAnchors, runtime_trace_manifest: ShadowTraceManifest) -> ValidationReport",
            "validate_cutover_eligibility(candidate_root: Path, anchors: ReviewedTrustAnchors, accepted_stage_a: ReviewedStageAAcceptance) -> ValidationReport",
        ],
        "internal_adapter_entrypoints": [
            "resolve_artifact_source(candidate_root: Path, exact_run_root: Path, expected_tree_sha256: str) -> ArtifactSource",
            "_validate_prototype_integrity_source(source: ArtifactSource, anchors: ReviewedTrustAnchors) -> ValidationReport",
            "_validate_write_safety_source(source: ArtifactSource, anchors: ReviewedTrustAnchors, writer_probe: WriterProbe) -> ValidationReport",
            "_validate_shadow_parity_source(source: ArtifactSource, anchors: ReviewedTrustAnchors, runtime_trace_manifest: ShadowTraceManifest) -> ValidationReport",
            "_validate_cutover_eligibility_source(source: ArtifactSource, anchors: ReviewedTrustAnchors, accepted_stage_a: ReviewedStageAAcceptance) -> ValidationReport",
        ],
        "same_public_name_may_not_have_path_and_artifact_source_overloads": True,
        "all_public_entrypoints_resolve_and_verify_artifact_source_before_validation": True,
        "reviewed_trust_anchors_are_loaded_from_git_verified_review_not_candidate_tree": True,
        "stage_a_acceptance_is_loaded_from_git_verified_review_not_candidate_tree": True,
        "public_validators_accept_only_values_returned_by_external_git_verified_loaders": True,
    }
    read_api = {
        "module_path_after_separate_implementation_authorization": "formal/python/toe/loop_control_registry_v1.py",
        "entrypoints": guardrail["api_contract"]["read_api"],
        "new_api_write_entrypoint_exists": False,
        "history_lookup_loads_only_index_selected_shard": True,
        "integrity_verification_bypass_parameter_allowed": False,
        "missing_and_ambiguous_ids_raise_distinct_typed_errors": True,
        "missing_record_exception": "RegistryRecordNotFoundError",
        "ambiguous_record_exception": "AmbiguousRegistryRecordIdError",
        "read_module_separate_from_write_module": True,
        "writes_are_prohibited_during_shadow_trace": True,
    }
    deterministic_packing = {
        "input_order": "SORT_HISTORY_RECORDS_BY_RECORD_ID_UTF8_BYTEWISE_ASCENDING",
        "line_bytes": "HISTORY_PAYLOAD_COMPACT_JSON_v1_PLUS_ONE_LF_NO_BOM_FINITE_NO_DUPLICATE_KEYS",
        "maximum_uncompressed_shard_bytes": 5242880,
        "packing": (
            "APPEND_NEXT_LINE_UNLESS_RESULT_WOULD_EXCEED_MAXIMUM_THEN_CLOSE_NONEMPTY_"
            "SHARD_AND_START_NEXT"
        ),
        "oversized_single_record": "FAIL_CLOSED",
        "sequence_index_origin": 0,
        "filename": "history/shards/LOOP_CONTROL_HISTORY_{sequence_index:04d}.jsonl",
        "maximum_sequence_index": 9999,
        "record_id_root": "JOIN_RECORD_IDS_IN_SHARD_ORDER_WITH_LF_NO_TERMINAL_LF_SHA256",
        "shard_id": (
            "lcs1:PLUS_SHA256_OF_HISTORY_SHARD_ID_v1_COMPACT_JSON_PREIMAGE_BINDING_"
            "SEQUENCE_PATH_RANGE_COUNT_RECORD_ROOT_CONTENT_SHA256_AND_SIZE"
        ),
        "shard_id_domain_value": "LOOP_CONTROL_SHARD_ID_v1",
        "shard_id_preimage_fields": [
            "domain",
            "sequence_index",
            "path",
            "first_record_id",
            "last_record_id",
            "record_count",
            "record_id_root_sha256",
            "sha256",
            "uncompressed_size_bytes",
        ],
        "shard_id_preimage_serializer": (
            "UTF8_SORTED_KEYS_COMMA_COLON_SEPARATORS_ALLOW_NAN_FALSE_NO_WHITESPACE_"
            "NO_TERMINAL_LF"
        ),
        "empty_shards_allowed": False,
        "two_independent_regenerations_must_be_byte_identical": True,
    }
    lifecycle = {
        "current_state": "PREPARATION_ONLY_REVIEW_REQUIRED_NOT_SELECTED",
        "stage_0_packet_review": {
            "required": True,
            "execution_authorized_before_acceptance": False,
            "selection_or_target_rotation_authorized": False,
            "accepted_review_may_authorize_only": EXECUTION_TARGET,
            "accepted_review_must_bind_packet_contract_and_review_commit": True,
            "accepted_review_may_authorize_stage_a_only": True,
            "stage_b_requires_versioned_successor_after_independent_stage_a_acceptance": True,
        },
        "stage_a_precutover_execution_after_separate_authorization": {
            "primary_control_count": 51,
            "primary_control_ids": primary_stage_a,
            "readiness_control_count": 7,
            "readiness_control_ids": readiness_stage_a,
            "distinct_control_count": 58,
            "runtime_contract_control_count": len(RUNTIME_NEGATIVE_CONTROLS),
            "total_stage_a_control_count": 58 + len(RUNTIME_NEGATIVE_CONTROLS),
            "control_result_order": primary_stage_a + readiness_stage_a,
            "each_result_binds_expected_and_observed_decision_error_set_profile_"
            "baseline_before_after_and_isolation": True,
            "control_results_root_preimage": (
                "UTF8_DOMAIN_LOOP_CONTROL_STAGE_A_CONTROL_RESULTS_ROOT_v1_NUL_"
                "PLUS_COMPACT_CANONICAL_RESULT_ROWS_JOINED_BY_LF_NO_TERMINAL_LF"
            ),
            "runtime_contract_results_root_preimage": (
                "UTF8_DOMAIN_LOOP_CONTROL_STAGE_A_RUNTIME_CONTRACT_RESULTS_ROOT_v1_"
                "NUL_PLUS_COMPACT_CANONICAL_RESULT_ROWS_JOINED_BY_LF_NO_TERMINAL_LF"
            ),
            "profile_control_roots_are_sha256_of_ordered_control_ids_joined_by_lf_"
            "without_terminal_lf": True,
            "cutover_control_ids_excluded": [
                "REGISTRY-V1-NC-044",
                "REGISTRY-READINESS-V1-RC-001",
            ],
            "cutover_control_exclusion_reasons": {
                "REGISTRY-V1-NC-044": (
                    "STAGE_A_DUAL_READ_SHADOW_REQUIRES_THE_LEGACY_MONOLITH_READER_"
                    "TO_REMAIN_ACTIVE"
                ),
                "REGISTRY-READINESS-V1-RC-001": (
                    "CUTOVER_PROFILE_CLOSURE_REQUIRES_AN_INDEPENDENTLY_ACCEPTED_"
                    "STAGE_A_SHADOW_BINDING"
                ),
            },
            "final_all_controls_passed_harness_report_allowed": False,
            "outputs_require_independent_review": True,
        },
        "stage_a_independent_review": {
            "must_bind": [
                "candidate_tree_sha256",
                "implementation_commit_and_tree_sha256",
                "consumer_rescan_source_commit_and_delta_root",
                "shadow_manifest_path_sha256_run_id",
                "custody_and_reconstruction_evidence",
                "source_and_authority_hashes_after_run",
            ],
            "acceptance_required_before_any_stage_b_successor_can_be_prepared": True,
            "review_does_not_itself_authorize_stage_b": True,
            "regeneration_and_consumer_rescan_source_is_exact_bound_implementation_commit": True,
            "later_execution_or_review_commit_must_not_replace_implementation_source_scan": True,
            "committed_execution_evidence_is_read_through_git_by_path_and_hash": True,
        },
        "stage_b_full_harness_deferred_obligation": {
            "authorized_or_executable_under_this_contract": False,
            "versioned_successor_packet_and_independent_review_required": True,
            "accepted_stage_a_manifest_must_be_frozen_by_path_and_sha256": True,
            "candidate_comparison_and_dynamic_evidence_pointer_semantics_must_be_"
            "resolved_by_successor": True,
            "accepted_stage_a_object_is_supplied_from_independently_reviewed_git_binding": True,
            "candidate_nested_acceptance_is_compared_byte_for_byte_to_external_binding": True,
            "candidate_may_not_supply_or_rebind_stage_a_acceptance_authority": True,
            "rerun_all_controls_in_fresh_overlays": True,
            "primary_control_count": 52,
            "readiness_control_count": 8,
            "distinct_control_count": 60,
            "runtime_contract_control_count": len(RUNTIME_NEGATIVE_CONTROLS),
            "future_total_control_count": 60 + len(RUNTIME_NEGATIVE_CONTROLS),
            "effective_profile_invocation_count": 199,
            "shadow_profile_uses_current_run_trace_manifest": True,
            "cutover_profile_uses_previously_accepted_stage_a_shadow_manifest": True,
            "counts_are_frozen_obligations_not_execution_evidence": True,
        },
        "future_stage_b_review_boundary": {
            "required_after_successor_execution": True,
            "may_accept_only_read_only_prototype_evidence": True,
            "migration_cutover_or_authority_still_not_authorized": True,
        },
    }
    allowed_paths = {
        "future_tracked_implementation_paths_after_separate_authorization": [
            "formal/python/tools/loop_control_registry_sharding_read_only_prototype_execution.py",
            "formal/python/toe/loop_control_registry_v1.py",
            "formal/python/toe/loop_control_registry_v1_validator.py",
            "formal/python/tests/test_loop_control_registry_v1_production_controls.py",
        ],
        "tracked_implementation_responsibility_map": {
            "prototype_builder_and_execution_orchestrator": "formal/python/tools/loop_control_registry_sharding_read_only_prototype_execution.py",
            "read_only_registry_api": "formal/python/toe/loop_control_registry_v1.py",
            "closed_schemas_validator_and_control_harness": "formal/python/toe/loop_control_registry_v1_validator.py",
            "production_control_regressions": "formal/python/tests/test_loop_control_registry_v1_production_controls.py",
        },
        "runtime_base": protocol["prototype_paths"]["prototype_base_repo_relative"],
        "runtime_artifact_paths_relative_to_exact_run_root": runtime_artifact_paths,
        "stage_a_persisted_runtime_artifact_keys": [
            "current_projection",
            "history_index",
            "custody_payload",
            "custody_manifest",
            "consumer_source_map",
            "reconstruction_result",
            "runtime_shadow_trace",
            "runtime_shadow_trace_manifest",
            "validation_report",
            "reviewed_trust_anchors",
            "artifact_source_manifest",
            "writer_probe",
            "run_rollback_inventory",
            "stage_a_precutover_report",
            "runtime_run_manifest",
            "execution_preflight",
        ],
        "stage_a_transient_runtime_artifact_keys": ["compatibility_reconstruction"],
        "stage_a_forbidden_runtime_artifact_keys": [
            "control_harness_report",
            "stage_b_full_harness_result",
        ],
        "runtime_history_shard_directory": protocol["prototype_paths"]["history_shard_directory_relative_to_run_root"],
        "runtime_history_shard_filename_pattern": protocol["prototype_paths"]["history_shard_filename_pattern"],
        "runtime_write_invariant": "ONLY_ALLOWLISTED_PATHS_STRICTLY_WITHIN_EXACT_RESOLVED_RUN_ROOT",
        "prohibited_runtime_writes": [
            REGISTRY,
            MAINTENANCE_AUTHORITY,
            AUTHORITATIVE_SURFACES,
            READINESS_SOURCE,
            "formal/docs/release/loop_control",
            "ANY_PATH_OUTSIDE_EXACT_RUN_ID_PROTOTYPE_ROOT",
        ],
    }
    runtime_validator_entrypoints = [
        "validate_reviewed_trust_anchors_contract(payload: object, review_context: GitReviewContext) -> RuntimeContractReport",
        "validate_artifact_source_manifest_contract(payload: object, candidate_root: Path) -> RuntimeContractReport",
        "validate_writer_probe_contract(payload: object, observed_writes: WriteObservation) -> RuntimeContractReport",
        "validate_run_rollback_inventory_contract(payload: object, filesystem_delta: FilesystemDelta) -> RuntimeContractReport",
        "validate_typed_result_envelope_contract(payload: object) -> RuntimeContractReport",
        "validate_stage_a_precutover_report_contract(payload: object, expected_controls: StageAControlContract) -> RuntimeContractReport",
        "validate_stage_a_acceptance_binding_contract(payload: object, review_context: GitReviewContext) -> RuntimeContractReport",
        "validate_stage_b_full_harness_result_contract(payload: object, accepted_stage_a: ReviewedStageAAcceptance) -> RuntimeContractReport",
        "validate_runtime_run_manifest_contract(payload: object, observed_run: RunObservation) -> RuntimeContractReport",
        "validate_execution_preflight_contract(payload: object, git_context: GitExecutionContext) -> RuntimeContractReport",
        "validate_runtime_cross_document_invariants(artifacts: RuntimeArtifacts, candidate_root: Path) -> RuntimeContractReport",
    ]
    return {
        "authorization": {
            "contract_independent_review_required": True,
            "implementation_authorized_now": False,
            "prototype_execution_authorized_now": False,
            "control_harness_execution_authorized_now": False,
            "custody_payload_creation_authorized_now": False,
            "shadow_trace_execution_authorized_now": False,
            "consumer_migration_authorized": False,
            "new_api_writes_authorized": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "legacy_monolith_modification_or_retirement_authorized": False,
            "maintenance_target_rotation_authorized": False,
            "scientific_target_rotation_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "allowed_and_prohibited_paths": allowed_paths,
        "artifact_source_and_candidate_tree_contract": {
            "artifact_source_manifest_is_not_self_inventoried": True,
            "all_other_regular_run_root_artifacts_are_inventoried_exactly_once": True,
            "artifact_paths_are_unique_independent_of_kind_or_hash": True,
            "candidate_payload_kinds": [
                "CURRENT_PROJECTION",
                "HISTORY_INDEX",
                "HISTORY_SHARD",
                "CUSTODY_PAYLOAD",
            ],
            "candidate_payload_membership_is_derived_from_kind_and_exact_path": True,
            "fixed_path_to_artifact_kind": {
                runtime_artifact_paths[key]: kind
                for key, kind in runtime_artifact_kind_by_key.items()
            },
            "history_shard_path_to_artifact_kind": {
                "path_pattern": "^history/shards/LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$",
                "artifact_kind": "HISTORY_SHARD",
            },
            "candidate_supplied_artifact_kind_or_candidate_payload_flag_is_not_trusted": True,
            "kind_path_mismatch_is_rejected": True,
            "candidate_payload_excludes_reports_traces_manifests_and_control_results": True,
            "inventory_row_fields": [
                "artifact_kind",
                "candidate_payload",
                "path",
                "sha256",
                "size_bytes",
            ],
            "row_serializer": (
                "UTF8_SORTED_KEYS_COMMA_COLON_SEPARATORS_ALLOW_NAN_FALSE_"
                "NO_WHITESPACE_NO_TERMINAL_LF"
            ),
            "row_order": "PATH_UTF8_BYTEWISE_ASCENDING",
            "inventory_root_preimage": (
                "UTF8_DOMAIN_LOOP_CONTROL_RUN_ARTIFACT_INVENTORY_ROOT_v1_NUL_"
                "PLUS_ROWS_JOINED_BY_LF_NO_TERMINAL_LF"
            ),
            "candidate_tree_root_preimage": (
                "UTF8_DOMAIN_LOOP_CONTROL_CANDIDATE_PAYLOAD_TREE_ROOT_v1_NUL_"
                "PLUS_CANDIDATE_ROWS_JOINED_BY_LF_NO_TERMINAL_LF"
            ),
            "candidate_tree_is_independent_of_run_id_and_stage_reports": True,
            "consumer_source_map_and_custody_manifest_are_stage_evidence_not_candidate_payload": True,
            "stage_a_history_index_binds_the_stage_a_consumer_and_custody_evidence_"
            "pointers": True,
            "dynamic_pointer_changes_may_change_raw_candidate_tree_and_are_deferred_"
            "to_stage_b_successor": True,
            "compatibility_reconstruction_is_transient_and_removed_after_result_binding": True,
            "transient_paths_excluded_from_final_inventory": [
                runtime_artifact_paths["compatibility_reconstruction"]
            ],
            "stage_a_candidate_tree_is_frozen_through_stage_a_independent_review": True,
            "stage_b_candidate_comparison_semantics_deferred_to_versioned_successor": True,
            "cross_document_invariants": [
                "RUN_ID_EQUAL_ACROSS_ALL_RUNTIME_DOCUMENTS",
                "PATH_SHA256_SIZE_MATCH_ACTUAL_BYTES",
                "IDENTITY_OBJECTS_MATCH_INVENTORY_ROWS",
                "STANDALONE_SCHEMA_PATHS_APPEAR_EXACTLY_ONCE_WHEN_STAGE_APPLICABLE",
                "CANDIDATE_PAYLOAD_COUNT_EQUALS_DERIVED_PAYLOAD_ROWS",
                "EVIDENCE_COUNT_EQUALS_DERIVED_NONPAYLOAD_ROWS",
            ],
            "candidate_provided_roots_are_recomputed_not_trusted": True,
        },
        "canonical_interface_and_adapter_contract": canonical_api,
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "control_harness_contract": {
            "control_error_map": deepcopy(protocol["control_error_map"]),
            "control_error_map_sha256": protocol["control_error_map_sha256"],
            "primary_controls": controls,
            "readiness_controls": readiness,
            "profile_composition": deepcopy(protocol["validator_profile_composition"]),
            "success_invariants": deepcopy(protocol["success_report_invariants"]),
            "execution_complete": False,
        },
        "custody_contract": {
            "contract_binding": source["bindings"][CUSTODY_CONTRACT],
            "execution_procedure": deepcopy(protocol["byte_custody_execution_procedure"]),
            "compressed_size_and_sha256_are_realized_execution_values": True,
            "reference_compressed_hash_is_non_normative": True,
        },
        "deterministic_projection_contract": deepcopy(guardrail["current_projection_contract"]),
        "deterministic_shard_packing_contract": deterministic_packing,
        "external_bindings": source["bindings"],
        "execution_preflight_contract": {
            "must_run_before_any_prototype_output_is_created": True,
            "accepted_packet_review_commit_is_distinct_from_v3_source_commit": True,
            "accepted_packet_review_commit_must_be_verified_ancestor_of_implementation_commit": True,
            "head_main_origin_main_must_equal_authorized_implementation_commit": True,
            "implementation_tree_and_source_hashes_must_be_bound": True,
            "implementation_source_manifest_paths": allowed_paths[
                "future_tracked_implementation_paths_after_separate_authorization"
            ],
            "implementation_source_manifest_row": "PATH_NUL_GIT_BLOB_OID_NUL_GIT_MODE",
            "implementation_source_manifest_order": "PATH_UTF8_BYTEWISE_ASCENDING",
            "implementation_tree_sha256_preimage": (
                "UTF8_DOMAIN_LOOP_CONTROL_READ_ONLY_PROTOTYPE_IMPLEMENTATION_TREE_v1_"
                "NUL_PLUS_MANIFEST_ROWS_JOINED_BY_LF_NO_TERMINAL_LF"
            ),
            "implementation_tree_sha256_recomputed_from_clean_git_commit": True,
            "implementation_commit_diff_from_authorization_review_is_limited_to_"
            "authorized_implementation_paths": True,
            "worktree_must_be_clean": True,
            "execution_must_use_fresh_detached_checkout_of_implementation_commit": True,
            "all_external_bindings_and_protected_hashes_must_be_reverified": True,
            "record_count_must_equal": 4691,
            "baseline_classified_consumer_path_count_must_equal": 496,
            "baseline_consumer_map_sha256": EXPECTED[CONSUMER_MAP][0],
            "fresh_consumer_rescan_required_and_live_count_is_not_frozen_to_496": True,
            "every_baseline_and_new_consumer_row_requires_a_typed_disposition": True,
            "consumer_inventory_delta_row_fields": [
                "path",
                "delta_class",
                "baseline_consumer_id",
                "current_consumer_id",
                "baseline_source_sha256",
                "current_source_sha256",
                "consumer_role",
                "access_operation",
                "disposition",
                "disposition_reason",
            ],
            "consumer_inventory_rows_have_unique_paths": True,
            "consumer_inventory_row_order": "PATH_UTF8_BYTEWISE_ASCENDING",
            "consumer_inventory_delta_root_preimage": (
                "UTF8_DOMAIN_LOOP_CONTROL_CONSUMER_INVENTORY_DELTA_ROOT_v1_NUL_"
                "PLUS_COMPACT_CANONICAL_ROWS_JOINED_BY_LF_NO_TERMINAL_LF"
            ),
            "consumer_inventory_delta_root_is_recomputed": True,
            "delta_class_nullability_and_disposition_relations_are_semantically_"
            "validated": True,
            "current_consumer_path_count_is_derived_from_nonretired_rows": True,
            "candidate_values_cannot_satisfy_preflight": True,
            "any_mismatch_stops_before_run_root_creation": True,
        },
        "failure_and_rollback": deepcopy(protocol["failure_and_rollback"]),
        "historical_absence_transition": _historical_absence_transition(),
        "historical_gate_executable_transition": {
            "required_before_authorized_stage_a_implementation_paths_are_created": True,
            "performed_as_mechanical_change_in_this_preparation_tranche": True,
            "requires_acceptance_with_the_preparation_packet": True,
            "affected_executable_checks": CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION,
            "per_check_historical_boundary": HISTORICAL_CHECK_BOUNDARIES,
            "replacement_semantics": (
                "VERIFY_FORBIDDEN_PATH_ABSENCE_IN_EACH_FROZEN_HISTORICAL_GIT_TREE_"
                "NOT_IN_THE_FUTURE_CURRENT_WORKTREE"
            ),
            "permanently_forbidden_production_authority_paths": FORBIDDEN_TRANSITION_PATHS[:4],
            "conditionally_allowed_after_accepted_packet_review": FORBIDDEN_TRANSITION_PATHS[4:],
            "packet_protocol_schema_review_and_lean_artifact_bytes_must_remain_unchanged": True,
            "all_existing_integrity_tests_remain_enrolled": True,
        },
        "history_payload_validation_algorithm": deepcopy(protocol["history_payload_validation_algorithm"]),
        "lifecycle": lifecycle,
        "path_and_run_safety": {
            "path_type_contract": deepcopy(protocol["path_type_contract"]),
            "repository_path_validation_algorithm": deepcopy(protocol["repository_path_validation_algorithm"]),
            "field_path_profile_map": deepcopy(protocol["field_path_profile_map"]),
            "field_path_profile_map_sha256": protocol["field_path_profile_map_sha256"],
        },
        "read_only_api_contract": read_api,
        "runtime_schema_count": len(runtime_schemas),
        "runtime_schema_artifact_mapping": runtime_schema_artifact_mapping,
        "runtime_schemas": runtime_schemas,
        "runtime_validator_contract": {
            "entrypoint_count": len(runtime_validator_entrypoints),
            "entrypoints": runtime_validator_entrypoints,
            "error_precedence": RUNTIME_ERROR_PRECEDENCE,
            "negative_control_count": len(RUNTIME_NEGATIVE_CONTROLS),
            "negative_controls": [
                {
                    "control_id": control_id,
                    "mutation": mutation,
                    "expected_exact_error": error,
                    "fresh_baseline": True,
                    "subsequent_controls_unmodified": True,
                }
                for control_id, mutation, error in RUNTIME_NEGATIVE_CONTROLS
            ],
            "schema_validation_runs_before_semantic_validation": True,
            "all_schemas_use_draft_2020_12_with_format_checker": True,
            "utc_timestamp_semantic_parser": (
                "datetime.fromisoformat(value.replace('Z', '+00:00'))_MUST_SUCCEED_"
                "AND_PRESERVE_UTC_AND_STARTED_MUST_NOT_EXCEED_FINISHED"
            ),
            "stage_a_control_results_root_is_recomputed": True,
            "each_stage_a_positive_baseline_must_pass_before_mutation": True,
            "each_stage_a_baseline_before_and_after_must_equal_report_candidate_tree": True,
            "candidate_internal_hashes_or_pass_flags_are_never_authoritative": True,
            "execution_complete": False,
        },
        "typed_result_envelope_validation": {
            "persistence": "IN_MEMORY_ONLY",
            "strict_base64_decode": "base64.b64decode(value, validate=True)",
            "canonical_base64_check": "base64.b64encode(decoded).decode('ascii') == value",
            "payload_sha256_is_hash_of_decoded_bytes": True,
            "value_payload_must_be_canonical_finite_duplicate_free_json_utf8": True,
            "exception_message_must_be_valid_utf8": True,
            "trace_persists_only_envelope_hashes_in_v3_closed_fields": [
                "legacy_result_sha256",
                "candidate_result_sha256",
            ],
            "v3_runtime_shadow_trace_schema_is_not_extended": True,
        },
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
            "CONTRACT_BUNDLE_20260711_v0"
        ),
        "shadow_trace_contract": deepcopy(protocol["runtime_shadow_tracing_protocol"]),
        "source_commit": SOURCE_COMMIT,
        "status": (
            "READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_PREPARED_REVIEW_REQUIRED_"
            "NO_IMPLEMENTATION_EXECUTION_MIGRATION_CUTOVER_OR_AUTHORITY"
        ),
        "validator_contract": {
            "engine_and_lock": deepcopy(protocol["validator_engine_and_lock_contract"]),
            "artifact_validator_interfaces": deepcopy(
                protocol["production_validator_interface"]["artifact_contract_validator_entrypoints"]
            ),
            "report_contract": deepcopy(protocol["production_validator_interface"]["report_contract"]),
            "integrity_bypass_parameter_allowed": False,
            "candidate_expected_values_are_authoritative": False,
            "json_schema_format_checker_required": True,
            "json_schema_validator_constructor": "Draft202012Validator(schema, format_checker=FormatChecker())",
        },
    }


def build_packet() -> dict[str, Any]:
    contract = build_contract()
    return {
        "authorization": {
            "independent_review_required": True,
            "packet_target_is_current_maintenance_authority": False,
            "implementation_authorized": False,
            "prototype_execution_selected_or_authorized": False,
            "control_harness_execution_authorized": False,
            "consumer_migration_authorized": False,
            "new_api_writes_authorized": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "maintenance_target_rotation_authorized": False,
            "scientific_target_rotation_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "boundary": {
            "production_reader_or_validator_implemented": False,
            "runtime_schemas_installed": False,
            "current_projection_prototype_created": False,
            "history_index_or_shards_created": False,
            "custody_payload_or_reconstruction_created": False,
            "runtime_shadow_trace_executed": False,
            "stage_a_58_controls_executed": False,
            "stage_b_60_controls_executed": False,
            "consumer_cutover_started": False,
            "legacy_monolith_modified_or_retired": False,
            "authority_cutover_or_target_rotation": False,
            "scientific_artifacts_or_claims_changed": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "contract_bundle": {
            "path": str(CONTRACT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sha256": _sha256(canonical_json_bytes(contract)),
        },
        "counts": {
            "historical_absence_gate_count": 9,
            "primary_control_count": 52,
            "readiness_control_count": 8,
            "stage_a_distinct_control_count": 58,
            "stage_a_runtime_contract_control_count": len(RUNTIME_NEGATIVE_CONTROLS),
            "stage_a_total_control_count": 58 + len(RUNTIME_NEGATIVE_CONTROLS),
            "stage_b_distinct_control_count": 60,
            "future_stage_b_total_control_count": 60 + len(RUNTIME_NEGATIVE_CONTROLS),
            "runtime_schema_count": contract["runtime_schema_count"],
        },
        "maintenance_target": MAINTENANCE_TARGET,
        "packet_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
            "PACKET_20260711_v0"
        ),
        "packet_target": PACKET_TARGET,
        "execution_target_recommended_not_selected": EXECUTION_TARGET,
        "review_target_recommended_not_selected": REVIEW_TARGET,
        "scientific_target": SCIENTIFIC_TARGET,
        "source_commit": SOURCE_COMMIT,
        "status": (
            "READ_ONLY_PROTOTYPE_EXECUTION_PREPARATION_PACKET_REVIEW_REQUIRED_"
            "NO_IMPLEMENTATION_EXECUTION_TARGET_ROTATION_MIGRATION_CUTOVER_OR_SCIENCE"
        ),
        "v3_acceptance_binding": {
            "accepted_review_path": V3_REVIEW,
            "accepted_review_sha256": EXPECTED[V3_REVIEW][0],
            "readiness_packet_sha256": EXPECTED[V3_PACKET][0],
            "protocol_bundle_sha256": EXPECTED[V3_PROTOCOL][0],
            "schema_bundle_sha256": EXPECTED[V3_SCHEMAS][0],
            "registry_migration_execution_readiness_accepted": False,
        },
    }


def build_all() -> dict[Path, bytes]:
    contract = canonical_json_bytes(build_contract())
    packet = canonical_json_bytes(build_packet())
    return {PACKET_PATH: packet, CONTRACT_PATH: contract}


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build or verify the read-only registry prototype execution preparation packet."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    for path, raw in build_all().items():
        if args.check:
            if not path.exists() or path.read_bytes() != raw:
                raise PrototypePreparationError(
                    f"read-only prototype preparation drift: {path.relative_to(REPO_ROOT)}"
                )
            print(
                f"read_only_prototype_preparation: OK "
                f"{path.relative_to(REPO_ROOT).as_posix()} sha256={_sha256(raw)}"
            )
        else:
            _atomic_write(path, raw)
            print(
                f"read_only_prototype_preparation: wrote "
                f"{path.relative_to(REPO_ROOT).as_posix()} sha256={_sha256(raw)}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
