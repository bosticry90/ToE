from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.loop_control_registry_integrity import (
    DEFAULT_REGISTRY_PATH,
    canonical_json_bytes as legacy_registry_canonical_json_bytes,
    load_registry,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEBT_BASELINE_PATH = REPO_ROOT / "formal/docs/release/TECHNICAL_DEBT_BASELINE_20260711_v0.json"
RETIREMENTS_PATH = (
    REPO_ROOT
    / "formal/docs/release/HISTORICAL_CURRENT_MIRROR_TEST_RETIREMENTS_20260711_v0.json"
)
CURRENT_AUTHORITY_PATH = (
    REPO_ROOT / "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
CONSUMER_INVENTORY_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_INVENTORY_20260711_v0.json"
)
GUARDRAIL_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v0.json"
)
MAINTENANCE_AUTHORITY_PATH = (
    REPO_ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
)
PYTHON_ROOT = REPO_ROOT / "formal/python"

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
SCIENTIFIC_PREVIOUS_TARGET = "prepare_pillar_seam_unit_mapping_ledger_guardrail_packet"
MAINTENANCE_TARGET = "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
MAX_CURRENT_PROJECTION_BYTES = 1 * 1024 * 1024
MAX_HISTORY_SHARD_BYTES = 5 * 1024 * 1024

CURRENT_SCHEMA_ID = "LOOP_CONTROL_CURRENT_v1"
INDEX_SCHEMA_ID = "LOOP_CONTROL_HISTORY_INDEX_v1"
RECORD_SCHEMA_ID = "LOOP_CONTROL_HISTORY_RECORD_v1"

CURRENT_REQUIRED_FIELDS = [
    "ACTIVE_LANE_v0",
    "CURRENT_LIVE_NEXT_TARGET_v0",
    "active_lane",
    "active_workstreams",
    "authority_role",
    "blockers",
    "claim_ceiling",
    "current_target",
    "current_target_evidence",
    "current_target_kind",
    "current_target_outcome",
    "current_target_report",
    "current_target_strict_outcome",
    "history_index_path",
    "maintenance_authority",
    "maintenance_authority_path",
    "nonpromotion_assertions",
    "previous_target",
    "schema_id",
    "schema_version",
    "source_legacy_registry_sha256",
    "status",
]

INDEX_SHARD_REQUIRED_FIELDS = [
    "first_record_id",
    "first_sequence",
    "last_record_id",
    "last_sequence",
    "path",
    "record_count",
    "schema_version",
    "sha256",
    "shard_id",
]

HISTORY_RECORD_REQUIRED_FIELDS = [
    "legacy_json_pointer",
    "payload",
    "payload_sha256",
    "record_id",
    "record_kind",
    "schema_id",
    "schema_version",
    "sequence",
]

NEGATIVE_CONTROLS = [
    "omitted_shard",
    "unindexed_extra_shard",
    "duplicate_record_within_or_across_shards",
    "incorrect_shard_hash",
    "incorrect_shard_record_count",
    "broken_index_sequence_or_id_range",
    "malformed_jsonl_row",
    "duplicate_exact_json_key_in_jsonl_row",
    "shard_exceeds_five_mib_ceiling",
    "path_traversal_or_path_outside_registry_directory",
    "two_active_scientific_targets",
    "projection_target_differs_from_active_workstream",
    "historical_record_promoted_into_current_projection",
    "nested_historical_object_replaces_current_root_schema",
    "unequal_current_aliases",
    "ambiguous_duplicate_legacy_workstream_id_without_stable_id",
    "maintenance_target_overwrites_scientific_target",
    "missing_legacy_json_pointer",
    "unaccounted_legacy_top_level_key",
    "legacy_reconstruction_semantic_mismatch",
    "scientific_target_fingerprint_change",
    "blocker_fingerprint_change",
    "claim_ceiling_fingerprint_change",
    "nonpromotion_fingerprint_change",
]

REGISTRY_HELPER_NAMES = {
    "active_workstream",
    "assert_current_target_consistent",
    "assert_forbidden_promotions_closed",
    "assert_frontier_matches_registry",
    "assert_historical_target_recorded",
    "assert_public_surfaces_match_registry",
    "current_target_state",
    "loop_registry",
    "skip_if_not_current_target",
    "workstream",
}


class GuardrailError(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise GuardrailError(f"duplicate exact JSON key: {key}")
        result[key] = value
    return result


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object)
    if not isinstance(value, dict):
        raise GuardrailError(f"expected JSON object: {path}")
    return value


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _repo_path(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def canonical_jsonl_line(payload: Any) -> bytes:
    return (
        json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"
    ).encode("utf-8")


def _stable_record_id(prefix: str, identity: str, payload: Any) -> str:
    payload_hash = _sha256_bytes(canonical_jsonl_line(payload)[:-1])
    return f"{prefix}:{identity}@{payload_hash[:16]}"


def _json_pointer_escape(value: str) -> str:
    return value.replace("~", "~0").replace("/", "~1")


def _json_pointer_unescape(value: str) -> str:
    return value.replace("~1", "/").replace("~0", "~")


def _authority_fingerprint_payload(current: dict[str, Any]) -> dict[str, Any]:
    return {
        "active_workstreams": current["active_workstreams"],
        "blockers": current["blockers"],
        "claim_ceiling": current["claim_ceiling"],
        "current_target": current["current_target"],
        "nonpromotion_assertions": current["nonpromotion_assertions"],
    }


def authority_fingerprint(current: dict[str, Any]) -> str:
    return _sha256_bytes(canonical_jsonl_line(_authority_fingerprint_payload(current))[:-1])


def _source_record_accounting(registry: dict[str, Any]) -> dict[str, Any]:
    metadata_rows: list[dict[str, Any]] = []
    line_sizes: list[int] = []
    record_ids: list[str] = []
    sequence = 0

    root_field_count = 0
    workstream_ids: list[str] = []
    for key, root_payload in registry.items():
        if key == "workstreams":
            for index, payload in enumerate(root_payload):
                legacy_id = str(payload["workstream_id"])
                record_id = _stable_record_id("WORKSTREAM", legacy_id, payload)
                record = {
                    "legacy_array_index": index,
                    "legacy_json_pointer": f"/workstreams/{index}",
                    "legacy_workstream_id": legacy_id,
                    "payload": payload,
                    "payload_sha256": _sha256_bytes(canonical_jsonl_line(payload)[:-1]),
                    "record_id": record_id,
                    "record_kind": "legacy_workstream",
                    "schema_id": RECORD_SCHEMA_ID,
                    "schema_version": 1,
                    "sequence": sequence,
                }
                encoded = canonical_jsonl_line(record)
                line_sizes.append(len(encoded))
                record_ids.append(record_id)
                workstream_ids.append(record_id)
                metadata_rows.append(
                    {
                        "legacy_json_pointer": record["legacy_json_pointer"],
                        "payload_sha256": record["payload_sha256"],
                        "record_id": record_id,
                        "record_kind": record["record_kind"],
                        "sequence": sequence,
                    }
                )
                sequence += 1
            continue

        payload = root_payload
        record_id = _stable_record_id("ROOT", _json_pointer_escape(key), payload)
        record = {
            "legacy_json_pointer": f"/{_json_pointer_escape(key)}",
            "payload": payload,
            "payload_sha256": _sha256_bytes(canonical_jsonl_line(payload)[:-1]),
            "record_id": record_id,
            "record_kind": "legacy_root_field",
            "schema_id": RECORD_SCHEMA_ID,
            "schema_version": 1,
            "sequence": sequence,
        }
        encoded = canonical_jsonl_line(record)
        line_sizes.append(len(encoded))
        record_ids.append(record_id)
        metadata_rows.append(
            {
                "legacy_json_pointer": record["legacy_json_pointer"],
                "payload_sha256": record["payload_sha256"],
                "record_id": record_id,
                "record_kind": record["record_kind"],
                "sequence": sequence,
            }
        )
        root_field_count += 1
        sequence += 1

    if len(record_ids) != len(set(record_ids)):
        raise GuardrailError("stable history record IDs are not unique")
    if max(line_sizes) > MAX_HISTORY_SHARD_BYTES:
        raise GuardrailError("a source record exceeds the proposed shard ceiling")

    shard_sizes: list[int] = []
    current_size = 0
    for line_size in line_sizes:
        if current_size and current_size + line_size > MAX_HISTORY_SHARD_BYTES:
            shard_sizes.append(current_size)
            current_size = 0
        current_size += line_size
    if current_size:
        shard_sizes.append(current_size)

    metadata_hash = _sha256_bytes(canonical_jsonl_line(metadata_rows)[:-1])
    pointer_hash = _sha256_bytes("\n".join(f"/{_json_pointer_escape(k)}" for k in sorted(registry)).encode("utf-8"))
    return {
        "estimated_deterministic_shard_count": len(shard_sizes),
        "estimated_shard_sizes_bytes": shard_sizes,
        "legacy_root_field_record_count": root_field_count,
        "legacy_top_level_json_pointer_count": len(registry),
        "legacy_top_level_json_pointer_set_sha256": pointer_hash,
        "max_encoded_source_record_bytes": max(line_sizes),
        "record_accounting_sha256": metadata_hash,
        "total_history_record_count": len(metadata_rows),
        "workstream_record_count": len(registry["workstreams"]),
        "workstream_stable_record_id_set_sha256": _sha256_bytes(
            "\n".join(sorted(workstream_ids)).encode("utf-8")
        ),
    }


def build_consumer_inventory() -> dict[str, Any]:
    registry_name = DEFAULT_REGISTRY_PATH.name
    direct_rows: list[dict[str, Any]] = []
    helper_importers: list[str] = []
    helper_registry_consumers: list[str] = []
    helper_path = "formal/python/tests/strict_physics_state_helpers.py"

    for path in sorted(PYTHON_ROOT.rglob("*.py"), key=lambda item: item.as_posix().casefold()):
        text = path.read_text(encoding="utf-8")
        rel = _repo_path(path)
        is_pytest_module = rel.startswith("formal/python/tests/") and path.name.startswith(
            "test_"
        )
        if is_pytest_module and "strict_physics_state_helpers" in text:
            helper_importers.append(rel)
            if any(re.search(rf"\b{re.escape(name)}\b", text) for name in REGISTRY_HELPER_NAMES):
                helper_registry_consumers.append(rel)
        if registry_name not in text:
            continue
        if rel == helper_path:
            role = "shared_test_helper"
        elif is_pytest_module:
            role = "pytest_module"
        elif rel.startswith("formal/python/tools/"):
            role = "production_or_migration_tool"
        else:
            role = "other_python_module"
        parse_signal = bool(re.search(r"\bjson\.loads?\s*\(", text))
        read_signal = any(token in text for token in ("read_text(", "read_bytes(", "open("))
        direct_rows.append(
            {
                "access_signals": {
                    "contains_file_read_call": read_signal,
                    "contains_json_parse_call": parse_signal,
                    "imports_strict_physics_state_helpers": "strict_physics_state_helpers" in text,
                },
                "path": rel,
                "role": role,
                "source_sha256": _sha256_file(path),
            }
        )

    direct_paths = {row["path"] for row in direct_rows}
    helper_importers = sorted(set(helper_importers))
    helper_registry_consumers = sorted(set(helper_registry_consumers))
    union_paths = direct_paths | set(helper_registry_consumers)
    retirements = _read_json(RETIREMENTS_PATH)
    retired_test_paths = {
        str(row["nodeid"]).split("::", 1)[0] for row in retirements["retired_tests"]
    }
    role_counts = Counter(row["role"] for row in direct_rows)
    direct_identity_hash = _sha256_bytes("\n".join(sorted(direct_paths)).encode("utf-8"))
    return {
        "boundary": {
            "consumer_migration_executed": False,
            "direct_consumer_growth_allowed_without_versioned_packet": False,
            "historical_path_citations_rewritten": False,
            "monolith_retired": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "direct_consumer_identity_set_sha256": direct_identity_hash,
        "direct_consumers": direct_rows,
        "metrics": {
            "direct_consumer_count": len(direct_rows),
            "direct_consumer_role_counts": dict(sorted(role_counts.items())),
            "direct_consumers_with_retired_test_nodes": len(direct_paths & retired_test_paths),
            "direct_or_helper_consumer_union_count": len(union_paths),
            "helper_importer_pytest_module_count": len(helper_importers),
            "helper_registry_behavior_consumer_pytest_module_count": len(
                helper_registry_consumers
            ),
            "legacy_reader_count_including_nonliteral_guardrail_reader": len(direct_rows) + 1,
        },
        "migration_order": [
            "formal/python/tests/strict_physics_state_helpers.py",
            "production_tools",
            "current_authority_and_freshness_tests",
            "remaining_direct_parsers_in_bounded_batches",
            "path_pointer_and_existence_only_consumers",
        ],
        "nonliteral_legacy_readers": [
            {
                "path": "formal/python/tools/loop_control_registry_sharding_guardrail.py",
                "role": "guardrail_baseline_reader_to_be_retained_only_as_migration_tool",
            }
        ],
        "schema_id": "LOOP_CONTROL_REGISTRY_CONSUMER_INVENTORY_20260711_v0",
        "shared_helper_importers": helper_importers,
        "shared_helper_registry_behavior_consumers": helper_registry_consumers,
        "status": "FROZEN_CONSUMER_INVENTORY_NO_MIGRATION_EXECUTED",
    }


def build_guardrail_packet(
    consumer_inventory: dict[str, Any], consumer_inventory_sha256: str
) -> dict[str, Any]:
    debt_baseline = _read_json(DEBT_BASELINE_PATH)
    registry_bytes = DEFAULT_REGISTRY_PATH.read_bytes()
    registry = load_registry(DEFAULT_REGISTRY_PATH)
    if registry_bytes != legacy_registry_canonical_json_bytes(registry):
        raise GuardrailError("source registry is not canonical deterministic JSON")

    debt_registry = debt_baseline["technical_debt_baselines"]["loop_control_registry"]
    if debt_registry["sha256"] != _sha256_bytes(registry_bytes):
        raise GuardrailError("registry differs from frozen technical-debt baseline")
    current_projection = registry["current_projection_v0"]
    if current_projection["current_target"] != SCIENTIFIC_TARGET:
        raise GuardrailError("scientific target changed before guardrail preparation")
    if current_projection["previous_target"] != SCIENTIFIC_PREVIOUS_TARGET:
        raise GuardrailError("previous scientific target changed before guardrail preparation")
    active_rows = [
        row for row in registry["workstreams"] if row["workstream_id"] == SCIENTIFIC_TARGET
    ]
    if len(active_rows) != 1 or active_rows[0]["status"] != "active":
        raise GuardrailError("expected exactly one active scientific workstream")
    active_row = active_rows[0]
    accounting = _source_record_accounting(registry)

    return {
        "api_contract": {
            "module": "formal/python/meta/loop_control_registry.py",
            "supported_functions": {
                "iter_history": "stream strict JSONL records through the verified shard index without loading all history",
                "load_current_state": "read and validate only LOOP_CONTROL_CURRENT_v1.json",
                "resolve_workstream": "resolve stable record IDs; reject ambiguous legacy workstream IDs",
                "verify_registry_index": "validate schemas, paths, hashes, sizes, counts, ranges, IDs, and complete accounting",
            },
            "deprecated_migration_only_function": {
                "name": "reconstruct_legacy_view",
                "rule": "may read all shards but may never determine current authority",
            },
            "only_supported_registry_reader_after_migration": True,
        },
        "authorization": {
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_kind": "registry_sharding_guardrail_preparation",
            "migration_execution_authorized": False,
            "monolith_retirement_authorized": False,
            "next_maintenance_target_selected": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_displaced": False,
        },
        "boundary": {
            "assertion_reconciliation_started": False,
            "axiom_or_opaque_review_started": False,
            "blocker_or_claim_status_changed": False,
            "current_projection_v1_generated": False,
            "history_index_or_shards_generated": False,
            "legacy_monolith_deleted_or_modified": False,
            "registry_consumer_migration_started": False,
            "scientific_artifacts_modified": False,
            "scientific_target_rotated": False,
            "snapshot_migration_or_deletion_started": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "completion_criteria_for_future_execution": [
            "every_legacy_top_level_field_and_workstream_record_is_accounted_for",
            "current_authority_loads_only_from_projection_under_one_mib",
            "history_resolves_only_through_verified_index_and_shards",
            "no_active_consumer_parses_or_reads_the_legacy_monolith",
            "authority_rotation_changes_only_current_projection_and_generated_mirrors",
            "legacy_baseline_view_reconstructs_to_the_frozen_source_sha256",
            "scientific_target_blockers_claim_ceiling_and_nonpromotion_state_are_unchanged",
            "monolith_retirement_occurs_only_after_independent_review_and_full_validation",
        ],
        "consumer_migration_contract": {
            "consumer_inventory_path": _repo_path(CONSUMER_INVENTORY_PATH),
            "consumer_inventory_sha256": consumer_inventory_sha256,
            "current_direct_consumer_count": consumer_inventory["metrics"][
                "direct_consumer_count"
            ],
            "current_direct_or_helper_union_count": consumer_inventory["metrics"][
                "direct_or_helper_consumer_union_count"
            ],
            "growth_gate": "direct consumer identity set and count may not increase without a versioned exception packet",
            "historical_citation_policy": "historical path citations remain unchanged and nonauthoritative",
            "target_end_state": "zero active runtime/test authority readers of the monolith; migration-only reconstruction tooling may remain explicit",
        },
        "current_projection_contract": {
            "active_workstream_required_fields": sorted(active_row),
            "current_target_state_authoritative_fields": registry[
                "current_target_state_authority_contract_v0"
            ]["authoritative_keys"],
            "forbidden_payload_classes": [
                "full_historical_workstream_catalog",
                "flattened_historical_packet_payloads",
                "historical_target_coverage_collections",
            ],
            "max_bytes": MAX_CURRENT_PROJECTION_BYTES,
            "required_root_fields": CURRENT_REQUIRED_FIELDS,
            "schema_id": CURRENT_SCHEMA_ID,
            "single_active_scientific_workstream_required": True,
        },
        "determinism_contract": {
            "canonical_json": "UTF-8, sorted keys, indent=2, terminal LF",
            "canonical_jsonl": "UTF-8, one sorted compact strict-JSON object per LF-terminated line",
            "generation_runs_required": 2,
            "legacy_reconstruction_must_match_source_bytes_and_sha256": True,
            "shard_packing": "source sequence order; close shard before next record would exceed exact byte ceiling",
        },
        "future_output_paths_declared_not_generated": {
            "compatibility_legacy_view": "formal/output/loop_control/LOOP_CONTROL_REGISTRY_LEGACY_VIEW_v1.json",
            "current_projection": "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
            "history_index": "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
            "history_shards": "formal/docs/release/loop_control/shards/LOOP_CONTROL_HISTORY_SHARD_<sequence>_v1.jsonl",
            "supported_reader_api": "formal/python/meta/loop_control_registry.py",
        },
        "history_contract": {
            "append_closed_shards": True,
            "index_shard_required_fields": INDEX_SHARD_REQUIRED_FIELDS,
            "max_shard_bytes": MAX_HISTORY_SHARD_BYTES,
            "record_required_fields": HISTORY_RECORD_REQUIRED_FIELDS,
            "record_schema_id": RECORD_SCHEMA_ID,
            "shard_index_schema_id": INDEX_SCHEMA_ID,
            "stable_record_id_rules": {
                "legacy_root_field": "ROOT:<escaped-root-key>@<first16-sha256-of-canonical-payload>",
                "legacy_workstream": "WORKSTREAM:<legacy-workstream-id>@<first16-sha256-of-canonical-payload>",
            },
            "strict_duplicate_key_rejection": True,
        },
        "negative_control_count": len(NEGATIVE_CONTROLS),
        "negative_controls": [
            {"control_id": control_id, "expected_result": "reject_fail_closed"}
            for control_id in NEGATIVE_CONTROLS
        ],
        "packet_id": "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_v0",
        "packet_result": "REGISTRY_SHARDING_AND_CURRENT_PROJECTION_CONTRACT_PREPARED_NO_MIGRATION_EXECUTION_OR_MONOLITH_RETIREMENT_AUTHORIZED",
        "record_accounting_contract": accounting,
        "schema_id": "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v0",
        "source_baseline": {
            "active_workstream_canonical_sha256": _sha256_bytes(
                canonical_jsonl_line(active_row)[:-1]
            ),
            "current_authority_path": _repo_path(CURRENT_AUTHORITY_PATH),
            "current_authority_sha256": _sha256_file(CURRENT_AUTHORITY_PATH),
            "current_projection": current_projection,
            "legacy_registry_canonical_reconstruction_sha256": _sha256_bytes(
                legacy_registry_canonical_json_bytes(registry)
            ),
            "legacy_registry_path": _repo_path(DEFAULT_REGISTRY_PATH),
            "legacy_registry_sha256": _sha256_bytes(registry_bytes),
            "legacy_registry_size_bytes": len(registry_bytes),
            "technical_debt_baseline_path": _repo_path(DEBT_BASELINE_PATH),
            "technical_debt_baseline_sha256": _sha256_file(DEBT_BASELINE_PATH),
        },
        "status": "PREPARED_GUARDRAIL_CONTRACT_ONLY_MIGRATION_NOT_RUN",
    }


def build_maintenance_authority(
    packet: dict[str, Any], packet_sha256: str, consumer_sha256: str
) -> dict[str, Any]:
    return {
        "boundary": {
            "maintenance_target_inserted_into_scientific_workstreams": False,
            "migration_execution_authorized": False,
            "next_maintenance_target_selected": False,
            "scientific_target_displaced": False,
            "scientific_target_rotated": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "current_maintenance_target": MAINTENANCE_TARGET,
        "current_maintenance_target_evidence": _repo_path(GUARDRAIL_PATH),
        "current_maintenance_target_evidence_sha256": packet_sha256,
        "current_maintenance_target_kind": "registry_sharding_guardrail_preparation",
        "current_maintenance_target_status": "PREPARED_CONTRACT_CURRENT_NO_EXECUTION_SUCCESSOR_SELECTED",
        "maintenance_consumer_inventory_path": _repo_path(CONSUMER_INVENTORY_PATH),
        "maintenance_consumer_inventory_sha256": consumer_sha256,
        "maintenance_program_source": _repo_path(DEBT_BASELINE_PATH),
        "maintenance_program_source_sha256": _sha256_file(DEBT_BASELINE_PATH),
        "schema_id": "CURRENT_MAINTENANCE_AUTHORITY_v0",
        "scientific_authority": {
            "current_target": SCIENTIFIC_TARGET,
            "previous_target": SCIENTIFIC_PREVIOUS_TARGET,
            "source": _repo_path(DEFAULT_REGISTRY_PATH),
            "source_sha256": packet["source_baseline"]["legacy_registry_sha256"],
        },
        "status": "ACTIVE_OPERATIONAL_NONSCIENTIFIC_MAINTENANCE_GUARDRAIL_ONLY",
    }


def build_outputs() -> dict[Path, bytes]:
    inventory = build_consumer_inventory()
    inventory_bytes = canonical_json_bytes(inventory)
    inventory_sha = _sha256_bytes(inventory_bytes)
    packet = build_guardrail_packet(inventory, inventory_sha)
    packet_bytes = canonical_json_bytes(packet)
    packet_sha = _sha256_bytes(packet_bytes)
    authority = build_maintenance_authority(packet, packet_sha, inventory_sha)
    return {
        CONSUMER_INVENTORY_PATH: inventory_bytes,
        GUARDRAIL_PATH: packet_bytes,
        MAINTENANCE_AUTHORITY_PATH: canonical_json_bytes(authority),
    }


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp_name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_name, path)
    finally:
        if os.path.exists(temp_name):
            os.unlink(temp_name)


def validate_candidate_layout(
    current: dict[str, Any], index: dict[str, Any], shards: dict[str, bytes]
) -> dict[str, Any]:
    if current.get("schema_id") != CURRENT_SCHEMA_ID:
        raise GuardrailError("current root schema is not canonical")
    missing_current = sorted(set(CURRENT_REQUIRED_FIELDS) - set(current))
    if missing_current:
        raise GuardrailError(f"current projection missing fields: {missing_current}")
    if current["current_target"] != current["CURRENT_LIVE_NEXT_TARGET_v0"]:
        raise GuardrailError("current target aliases diverge")
    if current["current_target"] != current["ACTIVE_LANE_v0"]:
        raise GuardrailError("active target aliases diverge")
    if current["current_target"] != current["active_lane"]:
        raise GuardrailError("lowercase active target alias diverges")
    if len(current["active_workstreams"]) != 1:
        raise GuardrailError("expected exactly one active scientific target")
    if current["active_workstreams"][0]["workstream_id"] != current["current_target"]:
        raise GuardrailError("projection target differs from active workstream")
    if any(key in current for key in ("legacy_json_pointer", "record_kind", "payload")):
        raise GuardrailError("historical record promoted into current projection")
    if current["maintenance_authority"]["current_maintenance_target"] == current[
        "current_target"
    ]:
        raise GuardrailError("maintenance target overwrites scientific target")
    if current["maintenance_authority"].get("scientific_target_displacement") is not False:
        raise GuardrailError("maintenance authority displaces scientific target")
    observed_authority = authority_fingerprint(current)
    if observed_authority != current["frozen_authority_fingerprint_sha256"]:
        raise GuardrailError("current authority fingerprint changed")

    if index.get("schema_id") != INDEX_SCHEMA_ID:
        raise GuardrailError("history index schema is not canonical")
    shard_rows = index.get("shards")
    if not isinstance(shard_rows, list) or not shard_rows:
        raise GuardrailError("history index has no shards")
    indexed_paths = [str(row.get("path", "")) for row in shard_rows]
    if set(indexed_paths) != set(shards):
        raise GuardrailError("indexed shard set differs from supplied shard set")

    all_records: list[dict[str, Any]] = []
    for shard in shard_rows:
        if sorted(shard) != sorted(INDEX_SHARD_REQUIRED_FIELDS):
            raise GuardrailError("shard index row fields are not canonical")
        rel = PurePosixPath(shard["path"])
        if rel.is_absolute() or ".." in rel.parts or not rel.parts or rel.parts[0] != "shards":
            raise GuardrailError("shard path escapes the registry directory")
        raw = shards[shard["path"]]
        if len(raw) > MAX_HISTORY_SHARD_BYTES:
            raise GuardrailError("shard exceeds exact byte ceiling")
        if _sha256_bytes(raw) != shard["sha256"]:
            raise GuardrailError("shard hash mismatch")
        records: list[dict[str, Any]] = []
        for raw_line in raw.splitlines():
            try:
                value = json.loads(raw_line, object_pairs_hook=_strict_object)
            except (json.JSONDecodeError, UnicodeDecodeError) as exc:
                raise GuardrailError("malformed strict JSONL row") from exc
            if not isinstance(value, dict):
                raise GuardrailError("JSONL row is not an object")
            if value.get("schema_id") != RECORD_SCHEMA_ID:
                raise GuardrailError("history record schema mismatch")
            if not set(HISTORY_RECORD_REQUIRED_FIELDS) <= set(value):
                raise GuardrailError("history record is missing required fields")
            if not value["legacy_json_pointer"]:
                raise GuardrailError("history record has no legacy JSON pointer")
            if _sha256_bytes(canonical_jsonl_line(value["payload"])[:-1]) != value[
                "payload_sha256"
            ]:
                raise GuardrailError("history payload hash mismatch")
            records.append(value)
        if len(records) != shard["record_count"]:
            raise GuardrailError("shard record count mismatch")
        if not records:
            raise GuardrailError("empty shard is not allowed")
        if (
            records[0]["sequence"] != shard["first_sequence"]
            or records[-1]["sequence"] != shard["last_sequence"]
            or records[0]["record_id"] != shard["first_record_id"]
            or records[-1]["record_id"] != shard["last_record_id"]
        ):
            raise GuardrailError("shard sequence or ID range mismatch")
        all_records.extend(records)

    ids = [row["record_id"] for row in all_records]
    sequences = [row["sequence"] for row in all_records]
    pointers = [row["legacy_json_pointer"] for row in all_records]
    if len(ids) != len(set(ids)) or len(sequences) != len(set(sequences)):
        raise GuardrailError("duplicate history record ID or sequence")
    if sequences != list(range(len(all_records))):
        raise GuardrailError("history sequences are not contiguous")
    if len(pointers) != len(set(pointers)):
        raise GuardrailError("duplicate legacy JSON pointer")

    reconstructed: dict[str, Any] = {}
    expected_workstream_index = 0
    for row in all_records:
        pointer = row["legacy_json_pointer"]
        if row["record_kind"] == "legacy_root_field":
            if not pointer.startswith("/") or "/" in pointer[1:]:
                raise GuardrailError("invalid root-field JSON pointer")
            reconstructed[_json_pointer_unescape(pointer[1:])] = row["payload"]
        elif row["record_kind"] == "legacy_workstream":
            match = re.fullmatch(r"/workstreams/(\d+)", pointer)
            if match is None:
                raise GuardrailError("invalid workstream JSON pointer")
            index_value = int(match.group(1))
            if index_value != expected_workstream_index:
                raise GuardrailError("legacy workstream indices are incomplete")
            if "workstreams" not in reconstructed:
                reconstructed["workstreams"] = []
            reconstructed["workstreams"].append(row["payload"])
            expected_workstream_index += 1
        else:
            raise GuardrailError("unknown history record kind")
    if set(reconstructed) != set(index["source_legacy_top_level_keys"]):
        raise GuardrailError("legacy top-level key accounting mismatch")
    if _sha256_bytes(legacy_registry_canonical_json_bytes(reconstructed)) != index[
        "source_legacy_canonical_sha256"
    ]:
        raise GuardrailError("legacy reconstruction semantic mismatch")
    return reconstructed


def resolve_candidate_workstream(
    records: list[dict[str, Any]], legacy_workstream_id: str, stable_record_id: str | None = None
) -> dict[str, Any]:
    matches = [
        row
        for row in records
        if row.get("record_kind") == "legacy_workstream"
        and row.get("legacy_workstream_id") == legacy_workstream_id
    ]
    if stable_record_id is not None:
        matches = [row for row in matches if row.get("record_id") == stable_record_id]
    if len(matches) != 1:
        raise GuardrailError(
            "legacy workstream ID is missing or ambiguous; stable record ID is required"
        )
    return matches[0]


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or verify the registry-sharding guardrail.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="Write canonical guardrail artifacts.")
    mode.add_argument("--check", action="store_true", help="Verify checked-in guardrail artifacts.")
    args = parser.parse_args()

    outputs = build_outputs()
    if args.check:
        mismatches = [path for path, data in outputs.items() if not path.exists() or path.read_bytes() != data]
        if mismatches:
            raise GuardrailError(f"guardrail artifact mismatch: {[str(path) for path in mismatches]}")
        for path, data in outputs.items():
            print(f"registry_sharding_guardrail: OK {_repo_path(path)} sha256={_sha256_bytes(data)}")
        return 0

    for path, data in outputs.items():
        _atomic_write(path, data)
        print(f"registry_sharding_guardrail: wrote {_repo_path(path)} sha256={_sha256_bytes(data)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
