from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

import pytest

from formal.python.tools import loop_control_registry_sharding_guardrail as guardrail


REVIEWED_GUARDRAIL_COMMIT = "c60cebde0116fa82d6e2e67053665711207ec408"
REVIEWED_ARTIFACT_HASHES = {
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_INVENTORY_20260711_v0.json": (
        "4dc376cedfafad55f950e62057113ab3f6695f28ad986a42e723fe451904aac4"
    ),
    "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v0.json": (
        "7371ff496fc8fd948e892e0136d380991c6f87128201d12fe7ff6f5df9ffa764"
    ),
    "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json": (
        "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b"
    ),
}


def _json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _fixture_current() -> dict:
    current = {
        "ACTIVE_LANE_v0": "scientific_target_v0",
        "CURRENT_LIVE_NEXT_TARGET_v0": "scientific_target_v0",
        "active_lane": "scientific_target_v0",
        "active_workstreams": [{"status": "active", "workstream_id": "scientific_target_v0"}],
        "authority_role": "current_scientific_projection",
        "blockers": ["blocker_a"],
        "claim_ceiling": {"level": 3, "status": "bounded"},
        "current_target": "scientific_target_v0",
        "current_target_evidence": "evidence.lean",
        "current_target_kind": "bounded_execution",
        "current_target_outcome": "PREPARED",
        "current_target_report": "report.json",
        "current_target_strict_outcome": "NO_PROMOTION",
        "history_index_path": "LOOP_CONTROL_HISTORY_INDEX_v1.json",
        "maintenance_authority": {
            "current_maintenance_target": "maintenance_target_v0",
            "scientific_target_displacement": False,
        },
        "maintenance_authority_path": "CURRENT_MAINTENANCE_AUTHORITY_v0.json",
        "nonpromotion_assertions": ["no_master_action_promotion"],
        "previous_target": "previous_scientific_target_v0",
        "schema_id": guardrail.CURRENT_SCHEMA_ID,
        "schema_version": 1,
        "source_legacy_registry_sha256": "0" * 64,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
    }
    current["frozen_authority_fingerprint_sha256"] = guardrail.authority_fingerprint(current)
    return current


def _history_record(
    *, sequence: int, record_kind: str, pointer: str, payload: object, identity: str
) -> dict:
    row = {
        "legacy_json_pointer": pointer,
        "payload": payload,
        "payload_sha256": hashlib.sha256(guardrail.canonical_jsonl_line(payload)[:-1]).hexdigest(),
        "record_id": guardrail._stable_record_id(record_kind.upper(), identity, payload),
        "record_kind": record_kind,
        "schema_id": guardrail.RECORD_SCHEMA_ID,
        "schema_version": 1,
        "sequence": sequence,
    }
    if record_kind == "legacy_workstream":
        row["legacy_array_index"] = int(pointer.rsplit("/", 1)[1])
        row["legacy_workstream_id"] = str(payload["workstream_id"])
    return row


def _fixture_layout() -> tuple[dict, dict, dict[str, bytes], dict]:
    legacy = {
        "CURRENT_LIVE_NEXT_TARGET_v0": "scientific_target_v0",
        "schema_id": "LOOP_CONTROL_REGISTRY_v0",
        "workstreams": [
            {"value": 1, "workstream_id": "duplicate_legacy_id"},
            {"value": 2, "workstream_id": "duplicate_legacy_id"},
        ],
    }
    records = [
        _history_record(
            sequence=0,
            record_kind="legacy_root_field",
            pointer="/CURRENT_LIVE_NEXT_TARGET_v0",
            payload=legacy["CURRENT_LIVE_NEXT_TARGET_v0"],
            identity="CURRENT_LIVE_NEXT_TARGET_v0",
        ),
        _history_record(
            sequence=1,
            record_kind="legacy_root_field",
            pointer="/schema_id",
            payload=legacy["schema_id"],
            identity="schema_id",
        ),
        _history_record(
            sequence=2,
            record_kind="legacy_workstream",
            pointer="/workstreams/0",
            payload=legacy["workstreams"][0],
            identity="duplicate_legacy_id",
        ),
        _history_record(
            sequence=3,
            record_kind="legacy_workstream",
            pointer="/workstreams/1",
            payload=legacy["workstreams"][1],
            identity="duplicate_legacy_id",
        ),
    ]
    shards = {
        "shards/part-0001.jsonl": b"".join(
            guardrail.canonical_jsonl_line(row) for row in records[:2]
        ),
        "shards/part-0002.jsonl": b"".join(
            guardrail.canonical_jsonl_line(row) for row in records[2:]
        ),
    }
    index = {
        "schema_id": guardrail.INDEX_SCHEMA_ID,
        "shards": [],
        "source_legacy_canonical_sha256": hashlib.sha256(
            guardrail.legacy_registry_canonical_json_bytes(legacy)
        ).hexdigest(),
        "source_legacy_top_level_keys": sorted(legacy),
    }
    _refresh_index(index, shards)
    return _fixture_current(), index, shards, legacy


def _strict_rows(raw: bytes) -> list[dict]:
    return [json.loads(line) for line in raw.splitlines()]


def _refresh_index(index: dict, shards: dict[str, bytes]) -> None:
    rows = []
    for ordinal, path in enumerate(sorted(shards), start=1):
        records = _strict_rows(shards[path])
        rows.append(
            {
                "first_record_id": records[0]["record_id"],
                "first_sequence": records[0]["sequence"],
                "last_record_id": records[-1]["record_id"],
                "last_sequence": records[-1]["sequence"],
                "path": path,
                "record_count": len(records),
                "schema_version": 1,
                "sha256": hashlib.sha256(shards[path]).hexdigest(),
                "shard_id": f"shard-{ordinal:04d}",
            }
        )
    index["shards"] = rows


def _replace_first_record(shards: dict[str, bytes], mutate) -> None:
    path = sorted(shards)[0]
    records = _strict_rows(shards[path])
    mutate(records[0])
    shards[path] = b"".join(guardrail.canonical_jsonl_line(row) for row in records)


def test_guardrail_v0_artifacts_are_immutable_reviewed_commit_evidence() -> None:
    for relative, expected_sha256 in REVIEWED_ARTIFACT_HASHES.items():
        reviewed = subprocess.run(
            ["git", "show", f"{REVIEWED_GUARDRAIL_COMMIT}:{relative}"],
            cwd=guardrail.REPO_ROOT,
            capture_output=True,
            check=True,
        ).stdout
        assert (guardrail.REPO_ROOT / relative).read_bytes() == reviewed
        assert hashlib.sha256(reviewed).hexdigest() == expected_sha256


def test_consumer_inventory_freezes_the_full_direct_and_helper_surface() -> None:
    inventory = _json(guardrail.CONSUMER_INVENTORY_PATH)
    metrics = inventory["metrics"]
    assert metrics["direct_consumer_count"] == 467
    assert metrics["direct_consumer_role_counts"] == {
        "production_or_migration_tool": 4,
        "pytest_module": 462,
        "shared_test_helper": 1,
    }
    assert metrics["helper_importer_pytest_module_count"] == 383
    assert metrics["helper_registry_behavior_consumer_pytest_module_count"] == 353
    assert metrics["direct_or_helper_consumer_union_count"] == 487
    assert metrics["direct_consumers_with_retired_test_nodes"] == 175
    assert len(inventory["direct_consumers"]) == 467
    assert len({row["path"] for row in inventory["direct_consumers"]}) == 467
    assert all(value is False for value in inventory["boundary"].values())


def test_packet_binds_complete_source_accounting_without_generating_shards() -> None:
    packet = _json(guardrail.GUARDRAIL_PATH)
    accounting = packet["record_accounting_contract"]
    assert accounting["legacy_root_field_record_count"] == 4_152
    assert accounting["workstream_record_count"] == 539
    assert accounting["total_history_record_count"] == 4_691
    assert accounting["legacy_top_level_json_pointer_count"] == 4_153
    assert accounting["max_encoded_source_record_bytes"] < guardrail.MAX_HISTORY_SHARD_BYTES
    assert accounting["estimated_deterministic_shard_count"] > 1
    assert max(accounting["estimated_shard_sizes_bytes"]) <= guardrail.MAX_HISTORY_SHARD_BYTES
    assert packet["history_contract"]["max_shard_bytes"] == 5 * 1024 * 1024
    assert packet["current_projection_contract"]["max_bytes"] == 1024 * 1024
    assert packet["source_baseline"]["legacy_registry_size_bytes"] == 52_340_650
    for path in packet["future_output_paths_declared_not_generated"].values():
        assert not (guardrail.REPO_ROOT / path).exists()


def test_guardrail_and_maintenance_authority_preserve_scientific_authority() -> None:
    packet = _json(guardrail.GUARDRAIL_PATH)
    authority = _json(guardrail.MAINTENANCE_AUTHORITY_PATH)
    assert packet["authorization"]["scientific_target"] == guardrail.SCIENTIFIC_TARGET
    assert packet["authorization"]["maintenance_target"] == guardrail.MAINTENANCE_TARGET
    assert packet["authorization"]["migration_execution_authorized"] is False
    assert packet["authorization"]["next_maintenance_target_selected"] is False
    assert all(value is False for value in packet["boundary"].values())
    assert authority["current_maintenance_target"] == guardrail.MAINTENANCE_TARGET
    assert authority["scientific_authority"]["current_target"] == guardrail.SCIENTIFIC_TARGET
    assert all(value is False for value in authority["boundary"].values())


def test_lean_certificate_binds_guardrail_artifact_hashes_and_nonaction() -> None:
    lean_path = (
        guardrail.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingGuardrailPacket.lean"
    )
    text = lean_path.read_text(encoding="utf-8")
    for path in (
        guardrail.GUARDRAIL_PATH,
        guardrail.CONSUMER_INVENTORY_PATH,
        guardrail.MAINTENANCE_AUTHORITY_PATH,
        guardrail.DEBT_BASELINE_PATH,
    ):
        assert hashlib.sha256(path.read_bytes()).hexdigest() in text
    assert guardrail.SCIENTIFIC_TARGET in text
    assert guardrail.MAINTENANCE_TARGET in text
    assert "migrationExecutionAuthorized : Bool := false" in text
    assert "legacyMonolithModifiedOrRetired : Bool := false" in text


def test_guardrail_freezes_supported_api_and_all_negative_controls() -> None:
    packet = _json(guardrail.GUARDRAIL_PATH)
    api = packet["api_contract"]
    assert sorted(api["supported_functions"]) == [
        "iter_history",
        "load_current_state",
        "resolve_workstream",
        "verify_registry_index",
    ]
    assert api["only_supported_registry_reader_after_migration"] is True
    assert packet["negative_control_count"] == len(guardrail.NEGATIVE_CONTROLS) == 24
    assert [row["control_id"] for row in packet["negative_controls"]] == guardrail.NEGATIVE_CONTROLS


def test_candidate_layout_validator_accepts_a_complete_fixture() -> None:
    current, index, shards, legacy = _fixture_layout()
    assert guardrail.validate_candidate_layout(current, index, shards) == legacy


def test_negative_control_omitted_shard_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    shards.pop(sorted(shards)[0])
    with pytest.raises(guardrail.GuardrailError, match="shard set"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_unindexed_extra_shard_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    shards["shards/extra.jsonl"] = next(iter(shards.values()))
    with pytest.raises(guardrail.GuardrailError, match="shard set"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_duplicate_record_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    path = sorted(shards)[1]
    shards[path] += shards[sorted(shards)[0]].splitlines(keepends=True)[0]
    _refresh_index(index, shards)
    with pytest.raises(guardrail.GuardrailError, match="duplicate history record"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_incorrect_shard_hash_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    index["shards"][0]["sha256"] = "0" * 64
    with pytest.raises(guardrail.GuardrailError, match="hash mismatch"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_incorrect_record_count_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    index["shards"][0]["record_count"] += 1
    with pytest.raises(guardrail.GuardrailError, match="record count"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_broken_range_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    index["shards"][0]["first_sequence"] += 1
    with pytest.raises(guardrail.GuardrailError, match="range mismatch"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_malformed_jsonl_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    path = sorted(shards)[0]
    shards[path] = b'{"truncated":\n'
    index["shards"][0]["sha256"] = hashlib.sha256(shards[path]).hexdigest()
    with pytest.raises(guardrail.GuardrailError, match="malformed strict JSONL"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_duplicate_exact_json_key_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    path = sorted(shards)[0]
    shards[path] = b'{"schema_id":"x","schema_id":"x"}\n'
    index["shards"][0]["sha256"] = hashlib.sha256(shards[path]).hexdigest()
    index["shards"][0]["record_count"] = 1
    with pytest.raises(guardrail.GuardrailError, match="duplicate exact JSON key"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_oversized_shard_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    path = sorted(shards)[0]
    shards[path] = b" " * (guardrail.MAX_HISTORY_SHARD_BYTES + 1)
    index["shards"][0]["sha256"] = hashlib.sha256(shards[path]).hexdigest()
    with pytest.raises(guardrail.GuardrailError, match="byte ceiling"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_path_traversal_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    old = index["shards"][0]["path"]
    raw = shards.pop(old)
    index["shards"][0]["path"] = "../escape.jsonl"
    shards["../escape.jsonl"] = raw
    with pytest.raises(guardrail.GuardrailError, match="escapes"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_two_active_scientific_targets_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    current["active_workstreams"].append({"status": "active", "workstream_id": "other"})
    with pytest.raises(guardrail.GuardrailError, match="exactly one"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_projection_active_target_mismatch_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    current["active_workstreams"][0]["workstream_id"] = "other"
    with pytest.raises(guardrail.GuardrailError, match="differs"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_historical_promotion_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    current["legacy_json_pointer"] = "/historical"
    with pytest.raises(guardrail.GuardrailError, match="promoted"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_root_schema_replacement_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    current["schema_id"] = guardrail.RECORD_SCHEMA_ID
    with pytest.raises(guardrail.GuardrailError, match="root schema"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_unequal_aliases_are_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    current["ACTIVE_LANE_v0"] = "other"
    with pytest.raises(guardrail.GuardrailError, match="aliases diverge"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_ambiguous_workstream_requires_stable_id() -> None:
    _, _, shards, _ = _fixture_layout()
    records = [row for raw in shards.values() for row in _strict_rows(raw)]
    with pytest.raises(guardrail.GuardrailError, match="ambiguous"):
        guardrail.resolve_candidate_workstream(records, "duplicate_legacy_id")
    stable_id = [
        row["record_id"] for row in records if row.get("legacy_workstream_id") == "duplicate_legacy_id"
    ][0]
    assert (
        guardrail.resolve_candidate_workstream(
            records, "duplicate_legacy_id", stable_record_id=stable_id
        )["record_id"]
        == stable_id
    )


def test_negative_control_maintenance_target_overwrite_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    current["maintenance_authority"]["current_maintenance_target"] = current["current_target"]
    with pytest.raises(guardrail.GuardrailError, match="overwrites"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_missing_legacy_pointer_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    _replace_first_record(shards, lambda row: row.__setitem__("legacy_json_pointer", ""))
    _refresh_index(index, shards)
    with pytest.raises(guardrail.GuardrailError, match="no legacy JSON pointer"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_unaccounted_top_level_key_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    index["source_legacy_top_level_keys"].append("missing_key")
    with pytest.raises(guardrail.GuardrailError, match="key accounting"):
        guardrail.validate_candidate_layout(current, index, shards)


def test_negative_control_legacy_reconstruction_mismatch_is_rejected() -> None:
    current, index, shards, _ = _fixture_layout()
    index["source_legacy_canonical_sha256"] = "0" * 64
    with pytest.raises(guardrail.GuardrailError, match="semantic mismatch"):
        guardrail.validate_candidate_layout(current, index, shards)


@pytest.mark.parametrize(
    ("field", "replacement"),
    [
        ("current_target", "other_target"),
        ("blockers", ["other_blocker"]),
        ("claim_ceiling", {"level": 4, "status": "promoted"}),
        ("nonpromotion_assertions", []),
    ],
)
def test_negative_control_authority_fingerprint_changes_are_rejected(
    field: str, replacement: object
) -> None:
    current, index, shards, _ = _fixture_layout()
    current[field] = replacement
    if field == "current_target":
        current["CURRENT_LIVE_NEXT_TARGET_v0"] = replacement
        current["ACTIVE_LANE_v0"] = replacement
        current["active_lane"] = replacement
        current["active_workstreams"][0]["workstream_id"] = replacement
    with pytest.raises(guardrail.GuardrailError, match="fingerprint changed"):
        guardrail.validate_candidate_layout(current, index, shards)
