from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any

from jsonschema import Draft202012Validator
from jsonschema.validators import validator_for

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REVIEWED_COMMIT = "6ce5f8389a8b4ac0cba2ab68ba9f4bb1e39743df"
BLOCKED_V0_BASELINE_COMMIT = "04b9200fa7b5b60df4a78f27b6d6fd8905101a22"
CAPTURED_AT_UTC = "2026-07-11T00:00:00Z"

PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "20260711_v1.json"
)
CONTRACT_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v1.json"
)
GENERATOR_REL = (
    "formal/python/tools/"
    "loop_control_registry_sharding_read_only_prototype_execution_packet_v1.py"
)
TEST_REL = (
    "formal/python/tests/"
    "test_loop_control_registry_sharding_read_only_prototype_execution_packet_v1.py"
)
LEAN_REL = (
    "formal/toe_formal/ToeFormal/Release/"
    "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV1.lean"
)
V0_CONTRACT_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v0.json"
)
REGISTRY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_REL = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
AUTHORITY_REL = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
READINESS_REL = "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
CONSUMER_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
REQUIREMENTS_REL = "requirements.ci.lock"
GOVERNANCE_MANIFEST_REL = "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"
CLOSED_SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3.json"
)
PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v3.json"
)
VALIDATOR_REL = "formal/python/toe/loop_control_registry_v1_validator.py"

OUTPUT_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v1.json"
)
OUTPUT_PATH = REPO_ROOT / OUTPUT_REL

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
SUCCESSOR_TARGET = (
    "prepare_loop_control_registry_sharding_read_only_prototype_execution_packet_v2"
)
REGISTRY_SHA256 = "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
PACKET_SHA256 = "bbefe919ffe2f4bd55538fdcee83a29be4e2d17d3d82d5391dede6b097270854"
CONTRACT_SHA256 = "ef1d51cd4a9a55c6affe0d7273d183eb69326474d0d0ab904ea13544dac1adff"

REVIEWED_INPUTS: dict[str, tuple[str, str, int]] = {
    PACKET_REL: (PACKET_SHA256, "d8b040ce202781fc65b28015e0917f2d0c272817", 2430),
    CONTRACT_REL: (CONTRACT_SHA256, "737c74f7ac66f145c347cd621e1fb9a6d03b8a39", 439612),
    GENERATOR_REL: (
        "a7a4430fe90e2ab3734bcc986e59c3990b55474b800e7c862cca7f06622ba7c0",
        "6dac76df3c6e10503c736c5ea5a5824f5e527767",
        93171,
    ),
    TEST_REL: (
        "0fefe5629ca38bbe1f25514e3379d08d19d277c7f9778638e9e61bfdf7fa52bd",
        "0d6fc6b5e6132e57c6da14f611bf674c33e00206",
        48406,
    ),
    LEAN_REL: (
        "b194acf8c2b806d7d675091fd31e9ab6ed7730dcccb78cee3f0fbcf25453b6b7",
        "52ab21eeb8aba64724e92c518c9338b38d7eb7df",
        3261,
    ),
    V0_CONTRACT_REL: (
        "272279d414591b25b3a519d22d92659f4a662ce1c9cbd5fadf3067f1eaa8f0bb",
        "abf0d597c05342a37a31db5e166dd2b5531cb888",
        392459,
    ),
    REGISTRY_REL: (REGISTRY_SHA256, "e6c5b3773dccd92fde9c0a8d486a56f993d6b235", 52340650),
    MAINTENANCE_REL: (
        "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
        "dca311d6abe38a872495c07f302d13ad886c0232",
        1768,
    ),
    AUTHORITY_REL: (
        "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
        "d46c5fb1966dcefc6b923776b7d94c4f5009b889",
        714575,
    ),
    READINESS_REL: (
        "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
        "85711a7c8cb0bc6a1f77d85cf3873726a5d6aa22",
        79556,
    ),
    CONSUMER_REL: (
        "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
        "9f9846ba735813c5b2b18f7a0115d88230a36600",
        469583,
    ),
    REQUIREMENTS_REL: (
        "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
        "bcc393883b90739408ed14d53d57dd0b42d0c2bd",
        741,
    ),
    GOVERNANCE_MANIFEST_REL: (
        "9ef73889d436e2cd8332b69b92e63a45947e9b6c9828ade5189dc069509e422c",
        "88bd9e9303949040246b95ff2976771197dd7c6f",
        43817,
    ),
}

AUTHORIZED_IMPLEMENTATION_PATHS = [
    "formal/python/tools/loop_control_registry_sharding_read_only_prototype_execution.py",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/python/tests/test_loop_control_registry_v1_production_controls.py",
]

NONLITERAL_READERS = [
    "formal/python/tests/test_loop_control_registry_envelope_integrity_gate.py",
    "formal/python/tests/test_loop_control_registry_integrity_repair_custody_gate.py",
    "formal/python/tools/loop_control_registry_sharding_guardrail.py",
]


class IndependentReviewError(ValueError):
    pass


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def compact_json_bytes(payload: Any) -> bytes:
    return json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _strict_json(raw: bytes) -> Any:
    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise IndependentReviewError(f"duplicate JSON key: {key}")
            output[key] = value
        return output

    def reject_constant(value: str) -> Any:
        raise IndependentReviewError(f"nonfinite JSON constant: {value}")

    return json.loads(raw, object_pairs_hook=pairs_hook, parse_constant=reject_constant)


def _git_blob(relative: str, commit: str = REVIEWED_COMMIT) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise IndependentReviewError(f"missing Git input: {commit}:{relative}")
    return result.stdout


def _git_blob_oid(relative: str, commit: str = REVIEWED_COMMIT) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _assert_canonical_json(relative: str) -> dict[str, Any]:
    raw = _git_blob(relative)
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw or not raw.endswith(b"\n"):
        raise IndependentReviewError(f"noncanonical JSON bytes: {relative}")
    payload = _strict_json(raw)
    if canonical_json_bytes(payload) != raw:
        raise IndependentReviewError(f"noncanonical JSON serialization: {relative}")
    return payload


def _reviewed_input_evidence() -> dict[str, dict[str, Any]]:
    observed = {}
    for path, (expected_sha, expected_blob, expected_size) in REVIEWED_INPUTS.items():
        raw = _git_blob(path)
        row = {
            "git_blob": _git_blob_oid(path),
            "path": path,
            "sha256": sha256(raw),
            "size_bytes": len(raw),
        }
        if row != {
            "git_blob": expected_blob,
            "path": path,
            "sha256": expected_sha,
            "size_bytes": expected_size,
        }:
            raise IndependentReviewError(f"reviewed input drift: {path}")
        observed[path] = row
    return observed


def _assert_closed_schema(schema: Any, path: str = "root") -> None:
    if isinstance(schema, dict):
        if schema.get("type") == "object" and schema.get("additionalProperties") is not False:
            raise IndependentReviewError(f"open object schema: {path}")
        for key, value in schema.items():
            _assert_closed_schema(value, f"{path}/{key}")
    elif isinstance(schema, list):
        for index, value in enumerate(schema):
            _assert_closed_schema(value, f"{path}/{index}")


def _topological_sort(graph: dict[str, list[str]]) -> list[str]:
    remaining = {node: set(dependencies) for node, dependencies in graph.items()}
    order: list[str] = []
    while remaining:
        ready = sorted(node for node, dependencies in remaining.items() if not dependencies)
        if not ready:
            raise IndependentReviewError("hash graph contains a cycle")
        for node in ready:
            order.append(node)
            remaining.pop(node)
            for dependencies in remaining.values():
                dependencies.discard(node)
    return order


def _has_property(schema: Any, property_name: str) -> bool:
    if isinstance(schema, dict):
        if property_name in schema.get("properties", {}):
            return True
        return any(_has_property(value, property_name) for value in schema.values())
    if isinstance(schema, list):
        return any(_has_property(value, property_name) for value in schema)
    return False


def _graph_review(contract: dict[str, Any]) -> dict[str, Any]:
    declared_outer = {
        row["node_id"]: list(row["binds"])
        for row in contract["hash_graph_contract"]["nodes"]
    }
    declared_outer_order = _topological_sort(declared_outer)
    declared_internal = {
        node: list(spec["binds"])
        for node, spec in contract["candidate_internal_hash_graph"]["nodes"].items()
    }
    declared_internal_order = _topological_sort(declared_internal)

    schema_bundle = _strict_json(_git_blob(CLOSED_SCHEMA_REL))
    schemas = schema_bundle["schemas"]
    for name, schema in schemas.items():
        validator_for(schema).check_schema(schema)
        _assert_closed_schema(schema, f"v3/{name}")

    required_fields = {
        "history_index": (
            "consumer_source_map_pointer",
            "custody_manifest_pointer",
            "shards",
        ),
        "current_projection": ("history_index_pointer",),
        "legacy_byte_custody_manifest": ("payload_identity",),
        "compatibility_reconstruction_result": ("custody_payload_identity",),
        "runtime_shadow_trace_manifest": ("consumer_scan_sha256", "event_jsonl_sha256"),
        "validation_report": ("candidate_root_sha256", "trust_anchor_sha256"),
    }
    for schema_name, fields in required_fields.items():
        for field in fields:
            if not _has_property(schemas[schema_name], field):
                raise IndependentReviewError(
                    f"expected hash-bearing field absent: {schema_name}/{field}"
                )

    actual_direct_content_dependencies = {
        "CONSUMER_SOURCE_MAP": ["BASELINE_CONSUMER_SOURCE_MAP"],
        "CONTROL_EVIDENCE": ["CORE_CANDIDATE_ROOT"],
        "CURRENT_PROJECTION": ["HISTORY_INDEX"],
        "CUSTODY_MANIFEST": ["CUSTODY_PAYLOAD"],
        "CUSTODY_PAYLOAD": [],
        "EXECUTION_PREFLIGHT": [],
        "HISTORY_INDEX": [
            "CONSUMER_SOURCE_MAP",
            "CUSTODY_MANIFEST",
            "HISTORY_SHARDS",
        ],
        "HISTORY_SHARDS": [],
        "RECONSTRUCTION_RESULT": ["CUSTODY_PAYLOAD"],
        "REVIEWED_TRUST_ANCHORS": [],
        "ROLLBACK_INVENTORY": [],
        "RUNTIME_TRACE": [],
        "RUNTIME_TRACE_MANIFEST": ["CONSUMER_SOURCE_MAP", "RUNTIME_TRACE"],
        "SOURCE_MANIFEST": [],
        "VALIDATION_REPORT": ["CORE_CANDIDATE_ROOT", "REVIEWED_TRUST_ANCHORS"],
        "WRITER_PROBE": [],
    }
    actual_internal_graph = {
        node: [dependency for dependency in dependencies if dependency in actual_direct_content_dependencies]
        for node, dependencies in actual_direct_content_dependencies.items()
    }
    actual_internal_order = _topological_sort(actual_internal_graph)

    source_bound_nodes = [
        node for node, dependencies in declared_internal.items() if "SOURCE_MANIFEST" in dependencies
    ]
    v0 = _strict_json(_git_blob(V0_CONTRACT_REL))
    content_schemas = list(schemas.values()) + [
        v0["runtime_schemas"][name]
        for name in (
            "execution_preflight",
            "reviewed_trust_anchors",
            "run_rollback_inventory",
            "writer_probe",
        )
    ] + [contract["runtime_schemas"]["control_evidence"]]
    source_manifest_property_count = sum(
        _has_property(schema, "source_manifest") for schema in content_schemas
    )

    candidate_kinds = set(
        contract["runtime_schemas"]["runtime_manifest"]["properties"]
        ["candidate_artifacts"]["items"]["properties"]["artifact_kind"]["enum"]
    )
    evidence_kinds = set(
        contract["runtime_schemas"]["runtime_manifest"]["properties"]
        ["evidence_artifacts"]["items"]["properties"]["artifact_kind"]["enum"]
    )
    outer_phase_conflict = (
        "HISTORY_INDEX" in candidate_kinds
        and {"CONSUMER_SOURCE_MAP", "CUSTODY_MANIFEST"}.issubset(evidence_kinds)
        and {"CONSUMER_SOURCE_MAP", "CUSTODY_MANIFEST"}.issubset(
            set(actual_direct_content_dependencies["HISTORY_INDEX"])
        )
    )
    if not outer_phase_conflict or source_manifest_property_count != 0:
        raise IndependentReviewError("expected graph-contract defect was not reproduced")

    mismatch_examples = [
        {
            "declared_dependencies": declared_internal["RUNTIME_TRACE_MANIFEST"],
            "node": "RUNTIME_TRACE_MANIFEST",
            "observed_direct_content_dependencies": actual_direct_content_dependencies[
                "RUNTIME_TRACE_MANIFEST"
            ],
        },
        {
            "declared_dependencies": declared_internal["VALIDATION_REPORT"],
            "node": "VALIDATION_REPORT",
            "observed_direct_content_dependencies": actual_direct_content_dependencies[
                "VALIDATION_REPORT"
            ],
        },
        {
            "declared_dependencies": declared_internal["CONTROL_EVIDENCE"],
            "node": "CONTROL_EVIDENCE",
            "observed_direct_content_dependencies": actual_direct_content_dependencies[
                "CONTROL_EVIDENCE"
            ],
        },
    ]
    return {
        "actual_direct_content_dependencies": actual_direct_content_dependencies,
        "actual_direct_content_graph_acyclic": True,
        "actual_direct_content_topological_order": actual_internal_order,
        "declared_candidate_graph_node_count": len(declared_internal),
        "declared_candidate_graph_topological_order": declared_internal_order,
        "declared_edge_semantics": contract["hash_graph_contract"]["edge_semantics"],
        "declared_graph_is_acyclic": True,
        "declared_graph_matches_hash_bearing_schema_fields": False,
        "declared_outer_graph_node_count": len(declared_outer),
        "declared_outer_topological_order": declared_outer_order,
        "declared_source_manifest_edge_count": len(source_bound_nodes),
        "explicit_source_manifest_identity_field_count_in_candidate_and_evidence_schemas": source_manifest_property_count,
        "mismatch_examples": mismatch_examples,
        "outer_core_before_evidence_phase_contract_matches_direct_hash_order": False,
        "outer_phase_conflict_reproduced": outer_phase_conflict,
        "review_conclusion": "B_BLOCKED_DECLARED_HASH_GRAPH_IS_NOT_BYTE_FAITHFUL",
    }


def _current_literal_paths() -> set[str]:
    result = subprocess.run(
        [
            "git",
            "grep",
            "-l",
            "-F",
            "LOOP_CONTROL_REGISTRY_v0.json",
            REVIEWED_COMMIT,
            "--",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    prefix = REVIEWED_COMMIT + ":"
    paths = {
        line[len(prefix) :] if line.startswith(prefix) else line
        for line in result.stdout.splitlines()
        if line.strip()
    }
    paths.discard(REGISTRY_REL)
    return paths


def _reviewed_tree_blob_map() -> dict[str, str]:
    result = subprocess.run(
        [
            "git",
            "ls-tree",
            "-r",
            "--full-tree",
            "--format=%(objectname) %(path)",
            REVIEWED_COMMIT,
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    output: dict[str, str] = {}
    for line in result.stdout.splitlines():
        object_name, path = line.split(" ", 1)
        output[path] = object_name
    return output


def _runtime_trace_required(path: str, raw: bytes) -> bool:
    if path in NONLITERAL_READERS or path == "formal/python/tools/loop_control_registry_integrity.py":
        return True
    if Path(path).suffix.lower() != ".py":
        return False
    text = raw.decode("utf-8", errors="replace")
    return any(token in text for token in ("read_text", "read_bytes", "json.load", "open("))


def _consumer_counterexample(
    contract: dict[str, Any], baseline: dict[str, Any]
) -> dict[str, Any]:
    schemas = _strict_json(_git_blob(CLOSED_SCHEMA_REL))["schemas"]
    baseline_row = next(row for row in baseline["consumers"] if row["runtime_trace_required"])
    candidate_row = {**baseline_row, "runtime_disposition": "OBSERVED_RUNTIME"}
    candidate_map = {
        "baseline": {
            "consumer_count": 496,
            "path": CONSUMER_REL,
            "sha256": REVIEWED_INPUTS[CONSUMER_REL][0],
            "source_commit": "6aba59d8d399b331db010f1f5f857075b9100b7f",
        },
        "consumers": [candidate_row],
        "current_scan": {
            "added_consumer_ids": [],
            "changed_consumer_ids": [],
            "consumer_count": 1,
            "removed_consumer_ids": [],
            "source_commit": REVIEWED_COMMIT,
            "unclassified_count": 0,
        },
        "schema_id": "LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2",
        "status": "STATIC_AND_RUNTIME_DISPOSITIONS_REQUIRED_BEFORE_CUTOVER",
    }
    map_raw = canonical_json_bytes(candidate_map)
    parity_hash = sha256(b"typed-parity-envelope")
    trace_event = {
        "access_granularity": "ROOT_DOCUMENT",
        "candidate_result_sha256": parity_hash,
        "comparison_mode": "CANONICAL_TYPED_ENVELOPE",
        "consumer_id": candidate_row["consumer_id"],
        "consumer_path": candidate_row["path"],
        "consumer_source_sha256": candidate_row["source_sha256"],
        "fields_accessed": [""],
        "legacy_result_sha256": parity_hash,
        "operation_id": "counterexample-read",
        "operation_type": "DIRECT_MONOLITH_READ",
        "resolved_registry_paths": {
            "candidate_prototype_path": "projection/LOOP_CONTROL_CURRENT_v1.prototype.json",
            "legacy_repository_path": REGISTRY_REL,
        },
        "run_id": "review-counterexample",
        "runtime_entrypoint": candidate_row["path"],
        "semantic_parity": True,
        "source_commit": REVIEWED_COMMIT,
        "trace_id": "lct1:" + sha256(candidate_row["consumer_id"].encode("utf-8")),
        "trace_schema_id": "LOOP_CONTROL_SHADOW_TRACE_EVENT_v3",
        "write_attempted": False,
        "write_paths": [],
    }
    trace_raw = compact_json_bytes(trace_event) + b"\n"
    trace_manifest = {
        "consumer_migration_performed": False,
        "consumer_scan_sha256": sha256(map_raw),
        "cutover_performed": False,
        "event_count": 1,
        "event_jsonl_sha256": sha256(trace_raw),
        "migration_batch_coverage_complete": True,
        "operation_class_coverage_complete": True,
        "required_consumer_count": 1,
        "required_consumers_observed": 1,
        "run_id": "review-counterexample",
        "schema_id": "LOOP_CONTROL_SHADOW_TRACE_MANIFEST_READINESS_v3",
        "semantic_mismatch_count": 0,
        "status": "COMPLETE_PARITY",
        "unclassified_consumer_count": 0,
        "unobserved_required_consumer_count": 0,
    }
    Draft202012Validator(schemas["consumer_source_map"]).validate(candidate_map)
    Draft202012Validator(schemas["runtime_shadow_trace_event"]).validate(trace_event)
    Draft202012Validator(schemas["runtime_shadow_trace_manifest"]).validate(trace_manifest)

    cross_document_keys = set(contract["cross_document_validation_algorithm"])
    consumer_reconciliation_keys = sorted(
        key for key in cross_document_keys if "consumer" in key or "trace" in key
    )
    return {
        "baseline_claimed_consumer_count": 496,
        "candidate_local_consumer_count": 1,
        "candidate_local_required_consumer_count": 1,
        "candidate_local_trace_event_count": 1,
        "candidate_map_sha256_after_internal_rebind": sha256(map_raw),
        "candidate_map_schema_valid": True,
        "candidate_trace_event_schema_valid": True,
        "candidate_trace_manifest_schema_valid": True,
        "candidate_trace_manifest_sha256_after_internal_rebind": sha256(
            canonical_json_bytes(trace_manifest)
        ),
        "cross_document_consumer_or_trace_reconciliation_keys": consumer_reconciliation_keys,
        "frozen_preflight_inventory_can_remain_496_while_candidate_map_is_1": True,
        "required_successor_error_code": "V1-E-CONSUMER-INVENTORY-CROSS-DOCUMENT",
        "self_rebound_truncation_rejected_by_reviewed_contract": False,
    }


def _line_number(source: str, needle: str) -> int:
    for index, line in enumerate(source.splitlines(), start=1):
        if needle in line:
            return index
    raise IndependentReviewError(f"validator evidence token not found: {needle}")


_CONSUMER_REVIEW_CACHE: dict[str, Any] | None = None


def _consumer_review(contract: dict[str, Any]) -> dict[str, Any]:
    global _CONSUMER_REVIEW_CACHE
    if _CONSUMER_REVIEW_CACHE is not None:
        return deepcopy(_CONSUMER_REVIEW_CACHE)
    baseline = _strict_json(_git_blob(CONSUMER_REL))
    baseline_paths = {row["path"] for row in baseline["consumers"]}
    literal_paths = _current_literal_paths()
    current_paths = literal_paths | set(NONLITERAL_READERS)
    added = sorted(current_paths - baseline_paths)
    removed = sorted(baseline_paths - current_paths)
    baseline_by_path = {row["path"]: row for row in baseline["consumers"]}
    tree_blobs = _reviewed_tree_blob_map()
    changed = sorted(
        path
        for path in baseline_paths & current_paths
        if tree_blobs[path] != baseline_by_path[path]["git_blob"]
    )
    unchanged = (baseline_paths & current_paths) - set(changed)
    runtime_required = sum(
        baseline_by_path[path]["runtime_trace_required"] for path in unchanged
    ) + sum(
        _runtime_trace_required(path, _git_blob(path))
        for path in sorted(set(added) | set(changed))
    )
    current_root = sha256("\n".join(sorted(current_paths)).encode("utf-8"))
    observed = {
        "added_consumer_count": len(added),
        "added_consumer_paths": added,
        "baseline_consumer_count": len(baseline_paths),
        "baseline_nonruntime_count": sum(
            not row["runtime_trace_required"] for row in baseline["consumers"]
        ),
        "baseline_runtime_required_count": sum(
            row["runtime_trace_required"] for row in baseline["consumers"]
        ),
        "changed_baseline_consumer_count": len(changed),
        "changed_baseline_consumer_paths": changed,
        "current_consumer_count_at_reviewed_commit": len(current_paths),
        "current_nonruntime_count_at_reviewed_commit": len(current_paths)
        - runtime_required,
        "current_runtime_required_count_at_reviewed_commit": runtime_required,
        "current_sorted_path_lf_root_sha256": current_root,
        "exact_literal_path_count_at_reviewed_commit": len(literal_paths),
        "explicit_nonliteral_reader_count": len(NONLITERAL_READERS),
        "removed_consumer_count": len(removed),
        "removed_consumer_paths": removed,
    }
    expected = {
        "added_consumer_count": 24,
        "baseline_consumer_count": 496,
        "baseline_nonruntime_count": 26,
        "baseline_runtime_required_count": 470,
        "changed_baseline_consumer_count": 3,
        "current_consumer_count_at_reviewed_commit": 520,
        "current_nonruntime_count_at_reviewed_commit": 35,
        "current_runtime_required_count_at_reviewed_commit": 485,
        "current_sorted_path_lf_root_sha256": "45a66d4608517dd823ae9b56fea3f54644cc0ae572e7e1160c07ce30593a04a5",
        "exact_literal_path_count_at_reviewed_commit": 517,
        "explicit_nonliteral_reader_count": 3,
        "removed_consumer_count": 0,
    }
    for key, value in expected.items():
        if observed[key] != value:
            raise IndependentReviewError(f"consumer rescan drift: {key}")

    validator_source = _git_blob(VALIDATOR_REL).decode("utf-8")
    validator_evidence = {
        "candidate_required_ids_derived_from_candidate_rows_line": _line_number(
            validator_source, "required_ids = {"
        ),
        "consumer_trace_validator_start_line": _line_number(
            validator_source, "def _validate_consumer_and_trace("
        ),
        "execution_preflight_validator_start_line": _line_number(
            validator_source, "def validate_execution_preflight_contract("
        ),
        "preflight_to_candidate_consumer_map_reconciliation_present": False,
    }
    _CONSUMER_REVIEW_CACHE = {
        **observed,
        "baseline_source_map_sha256": REVIEWED_INPUTS[CONSUMER_REL][0],
        "baseline_is_not_an_eternal_current_count": True,
        "candidate_self_rebind_counterexample": _consumer_counterexample(
            contract, baseline
        ),
        "production_validator_evidence_at_reviewed_commit": validator_evidence,
        "review_conclusion": "B_BLOCKED_CONSUMER_CUSTODY_NOT_EXTERNALLY_CROSS_BOUND",
    }
    return deepcopy(_CONSUMER_REVIEW_CACHE)


def _control_review(contract: dict[str, Any]) -> dict[str, Any]:
    profiles = contract["stage_a_control_contract"]["exact_control_profiles"]
    ids = [row["control_id"] for row in profiles]
    if len(ids) != 76 or len(set(ids)) != 76:
        raise IndependentReviewError("76-control identity reconciliation failed")
    id_root = sha256("\n".join(ids).encode("utf-8"))
    profile_root = sha256(
        b"LOOP_CONTROL_STAGE_A_V0_IMMUTABLE_CONTROL_PROFILE_ROOT_v1\0"
        + b"\n".join(compact_json_bytes(row) for row in profiles)
    )
    stage = contract["stage_a_control_contract"]
    if (
        id_root != stage["exact_control_id_root_sha256"]
        or profile_root != stage["exact_control_profile_root_sha256"]
    ):
        raise IndependentReviewError("76-control root drift")
    successor = stage["successor_regression_results"]
    successor_ids = [row["control_id"] for row in successor]
    if len(successor_ids) != 12 or len(set(successor_ids)) != 12:
        raise IndependentReviewError("successor regression identity drift")
    return {
        "control_definition_count": 76,
        "control_id_root_sha256": id_root,
        "control_profile_root_sha256": profile_root,
        "direct_orchestrator_invocation_remains_mandatory": True,
        "duplicate_control_id_count": 0,
        "inherited_control_count": 58,
        "primary_control_count": 51,
        "readiness_control_count": 7,
        "real_stage_a_controls_executed_by_review": 0,
        "runtime_contract_control_count": 18,
        "successor_regression_definition_count": 12,
        "successor_regression_execution_eligible": False,
        "successor_regressions_accepted_as_independent_production_mutations": 0,
        "successor_regressions_not_executed_reason": (
            "POSITIVE_BASELINE_FAILS_INDEPENDENT_GRAPH_AND_CONSUMER_CUSTODY_REVIEW"
        ),
    }


def _external_root_review(contract: dict[str, Any]) -> dict[str, Any]:
    rows = []
    for path, expected in sorted(
        contract["external_trust_contract"]["frozen_preparation_inputs"].items()
    ):
        raw = _git_blob(path, expected["source_commit"])
        observed = {
            "git_blob": _git_blob_oid(path, expected["source_commit"]),
            "path": path,
            "sha256": sha256(raw),
            "size_bytes": len(raw),
            "source_commit": expected["source_commit"],
        }
        if observed != expected:
            raise IndependentReviewError(f"frozen external root drift: {path}")
        rows.append(observed)
    return {
        "frozen_input_count": len(rows),
        "frozen_input_inventory_root_sha256": sha256(
            b"\n".join(compact_json_bytes(row) for row in rows)
        ),
        "packet_sha256_frozen_by_review": PACKET_SHA256,
        "contract_sha256_frozen_by_review": CONTRACT_SHA256,
        "registry_sha256_frozen_outside_candidate": REGISTRY_SHA256,
        "source_roots_verified": True,
        "candidate_consumer_inventory_externally_cross_bound": False,
    }


def _implementation_boundary_review(contract: dict[str, Any]) -> dict[str, Any]:
    paths = contract["implementation_path_contract"]["authorized_paths"]
    if paths != AUTHORIZED_IMPLEMENTATION_PATHS or len(set(paths)) != 4:
        raise IndependentReviewError("four-path implementation boundary drift")
    for path in paths:
        if _git_blob(path, BLOCKED_V0_BASELINE_COMMIT) != _git_blob(path):
            raise IndependentReviewError(f"blocked implementation path changed: {path}")
    return {
        "authorized_implementation_path_count": 4,
        "authorized_implementation_paths": paths,
        "fifth_implementation_path_authorized": False,
        "implementation_bytes_unchanged_from_blocked_v0_baseline": True,
        "review_integration_files_counted_as_implementation": False,
        "stage_a_implementation_authorized_by_this_review": False,
    }


_DETACHED_CACHE: dict[str, Any] | None = None


def _detached_determinism_review() -> dict[str, Any]:
    global _DETACHED_CACHE
    if _DETACHED_CACHE is not None:
        return deepcopy(_DETACHED_CACHE)
    with tempfile.TemporaryDirectory(prefix="toe-stage-a-v1-blocked-review-") as temporary:
        checkout = Path(temporary) / "reviewed"
        add = subprocess.run(
            ["git", "worktree", "add", "--detach", "--force", str(checkout), REVIEWED_COMMIT],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        if add.returncode != 0:
            raise IndependentReviewError(f"detached checkout failed: {add.stderr.strip()}")
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
        try:
            command = [
                sys.executable,
                "-m",
                "formal.python.tools.loop_control_registry_sharding_read_only_prototype_execution_packet_v1",
                "--write",
            ]
            runs = []
            snapshots = []
            for _ in range(2):
                result = subprocess.run(
                    command,
                    cwd=checkout,
                    capture_output=True,
                    text=True,
                    timeout=180,
                    env=env,
                    check=False,
                )
                if result.returncode != 0:
                    raise IndependentReviewError("detached successor regeneration failed")
                packet_raw = (checkout / PACKET_REL).read_bytes()
                contract_raw = (checkout / CONTRACT_REL).read_bytes()
                snapshots.append((packet_raw, contract_raw))
                runs.append(
                    {
                        "contract_sha256": sha256(contract_raw),
                        "packet_sha256": sha256(packet_raw),
                        "returncode": 0,
                    }
                )
            if (
                snapshots[0] != snapshots[1]
                or sha256(snapshots[0][0]) != PACKET_SHA256
                or sha256(snapshots[0][1]) != CONTRACT_SHA256
            ):
                raise IndependentReviewError("detached regeneration is not byte-identical")
            check = subprocess.run(
                command[:-1] + ["--check"],
                cwd=checkout,
                capture_output=True,
                text=True,
                timeout=180,
                env=env,
                check=False,
            )
            if check.returncode != 0:
                raise IndependentReviewError("detached successor check failed")
            focused = subprocess.run(
                [sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider", TEST_REL],
                cwd=checkout,
                capture_output=True,
                text=True,
                timeout=240,
                env=env,
                check=False,
            )
            combined = focused.stdout + "\n" + focused.stderr
            matched = re.search(r"(?:^|\s)(\d+) passed(?:\s|$)", combined)
            passed = int(matched.group(1)) if matched else 0
            if focused.returncode != 0 or passed != 27:
                raise IndependentReviewError(f"detached focused suite failed: {passed}")
            status = subprocess.run(
                ["git", "status", "--porcelain=v1"],
                cwd=checkout,
                capture_output=True,
                text=True,
                timeout=60,
                check=True,
            )
            if status.stdout:
                raise IndependentReviewError("detached checkout was contaminated")
        finally:
            remove = subprocess.run(
                ["git", "worktree", "remove", "--force", str(checkout)],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                timeout=180,
                check=False,
            )
            if remove.returncode != 0:
                subprocess.run(
                    ["git", "worktree", "prune"],
                    cwd=REPO_ROOT,
                    capture_output=True,
                    timeout=60,
                    check=False,
                )
                raise IndependentReviewError("detached checkout cleanup failed")
    generator_source = _git_blob(GENERATOR_REL).decode("utf-8")
    forbidden = [
        "datetime.now",
        "datetime.utcnow",
        "time.time(",
        "socket.gethostname",
        "os.getcwd(",
        "Path.cwd(",
    ]
    present = [token for token in forbidden if token in generator_source]
    if present:
        raise IndependentReviewError(f"ambient generator input found: {present}")
    _DETACHED_CACHE = {
        "canonical_json_allow_nan_false": "allow_nan=False" in generator_source,
        "detached_checkout_clean_after": True,
        "detached_focused_test_count": 27,
        "detached_regeneration_count": 2,
        "generator_check_passed": True,
        "host_or_temporary_absolute_path_embedded": False,
        "packet_and_contract_byte_identical_across_regenerations": True,
        "regeneration_results": runs,
        "wall_clock_or_ambient_branch_input_used": False,
    }
    return deepcopy(_DETACHED_CACHE)


def _authority_review(packet: dict[str, Any]) -> dict[str, Any]:
    maintenance = _strict_json(_git_blob(MAINTENANCE_REL))
    if maintenance["scientific_authority"]["current_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewError("scientific target drift")
    if maintenance["current_maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewError("maintenance target drift")
    if maintenance["boundary"]["migration_execution_authorized"] is not False:
        raise IndependentReviewError("migration execution was authorized")
    if packet["scientific_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewError("packet scientific target drift")
    if packet["maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewError("packet maintenance target drift")
    prototype = "formal/scratch/loop_control_registry_v1_prototype"
    exists = subprocess.run(
        ["git", "cat-file", "-e", f"{REVIEWED_COMMIT}:{prototype}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    ).returncode == 0
    if exists:
        raise IndependentReviewError("prototype path exists at reviewed commit")
    return {
        "authority_or_target_rotated": False,
        "maintenance_target": MAINTENANCE_TARGET,
        "migration_execution_authorized": False,
        "prototype_artifacts_created": False,
        "real_stage_a_execution_occurred": False,
        "registry_sha256": REGISTRY_SHA256,
        "scientific_target": SCIENTIFIC_TARGET,
        "stage_b_authorized": False,
        "unit_ledger_execution_occurred": False,
    }


def build_review() -> dict[str, Any]:
    packet = _assert_canonical_json(PACKET_REL)
    contract = _assert_canonical_json(CONTRACT_REL)
    if packet["contract_bundle"]["sha256"] != CONTRACT_SHA256:
        raise IndependentReviewError("packet/contract hash mismatch")
    if (
        packet["source_commit"] != BLOCKED_V0_BASELINE_COMMIT
        or contract["source_commit"] != BLOCKED_V0_BASELINE_COMMIT
    ):
        raise IndependentReviewError("blocked-v0 baseline commit drift")
    if len(contract["runtime_schemas"]) != 7:
        raise IndependentReviewError("runtime schema count drift")
    for name, schema in contract["runtime_schemas"].items():
        validator_for(schema).check_schema(schema)
        _assert_closed_schema(schema, f"runtime/{name}")

    graph = _graph_review(contract)
    consumers = _consumer_review(contract)
    if (
        graph["declared_graph_matches_hash_bearing_schema_fields"]
        or consumers["candidate_self_rebind_counterexample"]
        ["self_rebound_truncation_rejected_by_reviewed_contract"]
    ):
        raise IndependentReviewError("blocking review evidence was not reproduced")

    return {
        "accepted_corrections": {
            "historical_reciprocal_source_runtime_manifest_cycle_removed": True,
            "source_runtime_report_terminal_order_is_directional": True,
            "terminal_envelope_schema_present": True,
            "twelve_cycle_and_self_reference_regression_definitions_present": True,
            "v1_retained_as_versioned_preparation_evidence": True,
        },
        "authorization": {
            "authority_cutover_authorized": False,
            "bounded_stage_a_v1_attempt_authorized": False,
            "consumer_migration_authorized": False,
            "exact_four_path_stage_a_implementation_authorized": False,
            "legacy_monolith_modification_or_retirement_authorized": False,
            "maintenance_target_rotation_authorized": False,
            "new_registry_api_writes_authorized": False,
            "production_registry_migration_authorized": False,
            "release_or_publication_authorized": False,
            "scientific_claim_or_blocker_movement_authorized": False,
            "scientific_target_rotation_authorized": False,
            "stage_b_authorized": False,
            "unit_ledger_execution_authorized": False,
            "versioned_v2_successor_required": True,
        },
        "authority_and_nonclaim_review": _authority_review(packet),
        "blocked_v0_baseline_commit": BLOCKED_V0_BASELINE_COMMIT,
        "blocking_findings": [
            {
                "finding_id": "V1-IR-BLOCK-001-DECLARED-HASH-GRAPH-NOT-BYTE-FAITHFUL",
                "impact": (
                    "THE_DECLARED_HASH_EDGES_AND_OUTER_PHASE_ORDER_DO_NOT_MATCH_"
                    "THE_HASH_BEARING_FIELDS_REQUIRED_BY_THE_CLOSED_SCHEMAS"
                ),
                "required_disposition": "VERSIONED_SUCCESSOR_MUST_SEPARATE_CONTENT_HASH_EDGES_GENERATION_DEPENDENCIES_AND_INVENTORY_MEMBERSHIP",
                "severity": "BLOCKING",
            },
            {
                "finding_id": "V1-IR-BLOCK-002-CONSUMER-INVENTORY-CROSS-DOCUMENT-GAP",
                "impact": (
                    "A_TRUNCATED_CONSUMER_MAP_AND_TRACE_CAN_REBIND_CANDIDATE_LOCAL_"
                    "HASHES_WITHOUT_RECONCILIATION_TO_THE_FROZEN_BASELINE_AND_FRESH_PREFLIGHT_DELTA"
                ),
                "required_disposition": "ADD_V1_E_CONSUMER_INVENTORY_CROSS_DOCUMENT_AND_A_PERMANENT_SELF_REBOUND_TRUNCATION_CONTROL",
                "severity": "BLOCKING",
            },
            {
                "finding_id": "V1-IR-BLOCK-003-NO-INDEPENDENTLY-VALID-POSITIVE-LIFECYCLE-BASELINE",
                "impact": (
                    "COMPLETE_AND_POST_GENERATION_BLOCKED_LIFECYCLE_SATISFIABILITY_"
                    "CANNOT_BE_ACCEPTED_AND_THE_TWELVE_REGRESSIONS_CANNOT_BE_RUN_FROM_A_CLEAN_POSITIVE_BASELINE"
                ),
                "required_disposition": "SUCCESSOR_REVIEW_MUST_VALIDATE_REAL_CROSS_DOCUMENT_MODELS_AND_MUTATE_THEM_THROUGH_AN_INDEPENDENT_VALIDATOR",
                "severity": "BLOCKING",
            },
        ],
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumer_inventory_and_shadow_contract_review": consumers,
        "contract_bundle_sha256": CONTRACT_SHA256,
        "control_contract_review": _control_review(contract),
        "decision": "B_BLOCKED_REJECT_ONE_WAY_STAGE_A_V1_EXECUTION_AUTHORIZATION_REQUIRE_VERSIONED_V2_SUCCESSOR",
        "detached_clean_checkout_review": _detached_determinism_review(),
        "external_root_review": _external_root_review(contract),
        "graph_review": graph,
        "implementation_boundary_review": _implementation_boundary_review(contract),
        "lifecycle_satisfiability_review": {
            "complete_path_independently_proved_satisfiable": False,
            "post_generation_blocked_path_independently_proved_satisfiable": False,
            "preflight_failure_can_remain_diagnostic_only": True,
            "real_candidate_artifacts_created": False,
            "rejection_reason_codes": [
                "V1-IR-BLOCK-001-DECLARED-HASH-GRAPH-NOT-BYTE-FAITHFUL",
                "V1-IR-BLOCK-002-CONSUMER-INVENTORY-CROSS-DOCUMENT-GAP",
                "V1-IR-BLOCK-003-NO-INDEPENDENTLY-VALID-POSITIVE-LIFECYCLE-BASELINE",
            ],
            "runtime_schema_count": 7,
            "schema_closedness_verified": True,
            "stage_a_execution_authorized": False,
        },
        "packet_sha256": PACKET_SHA256,
        "recommended_successor": {
            "required_target": SUCCESSOR_TARGET,
            "requirements": [
                "DERIVE_THE_ARTIFACT_HASH_GRAPH_FROM_ACTUAL_SCHEMA_FIELDS_AND_BYTES",
                "SEPARATE_DIRECT_CONTENT_HASH_EDGES_FROM_GENERATION_DEPENDENCIES_AND_INVENTORY_ROOTS",
                "ADD_OR_REMOVE_SOURCE_MANIFEST_IDENTITY_FIELDS_TO_MATCH_THE_DECLARED_EDGE_SEMANTICS",
                "ALIGN_CORE_AND_EVIDENCE_PHASES_WITH_HISTORY_INDEX_HASH_DEPENDENCIES",
                "CROSS_BIND_BASELINE_CONSUMER_MAP_FRESH_TYPED_DELTA_CURRENT_MAP_AND_TRACE_ID_SET",
                "ADD_V1_E_CONSUMER_INVENTORY_CROSS_DOCUMENT_AND_SELF_REBOUND_TRUNCATION_REGRESSION",
                "RUN_SUCCESSOR_REGRESSIONS_AGAINST_REAL_MUTATED_LIFECYCLE_DOCUMENTS_THROUGH_AN_INDEPENDENT_VALIDATOR",
            ],
        },
        "review_id": "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_INDEPENDENT_REVIEW_20260711_v1",
        "review_scope": {
            "candidate_artifacts_created": False,
            "prototype_execution_attempted": False,
            "real_stage_a_preterminal_controls_executed": 0,
            "stage_b_executed": False,
            "successor_regression_definitions_reconciled": 12,
            "successor_regressions_accepted_as_production_mutations": 0,
        },
        "reviewed_commit": REVIEWED_COMMIT,
        "reviewed_inputs": _reviewed_input_evidence(),
        "schema_id": "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_INDEPENDENT_REVIEW_20260711_v1",
        "status": "B_BLOCKED_V1_CONTRACT_PRESERVED_NO_STAGE_A_STAGE_B_MIGRATION_CUTOVER_AUTHORITY_OR_SCIENCE",
    }


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
        description="Build or verify the blocked independent review of the one-way Stage-A v1 contract."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise IndependentReviewError("blocked Stage-A v1 independent review drift")
        print(f"stage_a_v1_independent_review: B_BLOCKED sha256={sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"stage_a_v1_independent_review: wrote B_BLOCKED sha256={sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
