from __future__ import annotations

import hashlib
import json
import subprocess

from formal.python.tools import loop_control_registry_sharding_guardrail_v1 as guardrail


EXPECTED_PACKET_SHA256 = "41994b0c1703d7f7f7ff7aeda217900a3136489f070ae55a88f2db10a13d12c0"
EXPECTED_CONSUMER_SHA256 = "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642"
EXPECTED_CUSTODY_SHA256 = "bc35c992c9b9fd7dd9c2e84ed6d5b89463b3ce8eb13dc2f7c7d1c539b4d23ce9"


def _payload(path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_v1_artifacts_are_deterministic_from_committed_inputs() -> None:
    artifacts = guardrail.build_all()
    expected = {
        guardrail.PACKET_PATH: EXPECTED_PACKET_SHA256,
        guardrail.CONSUMER_MAP_PATH: EXPECTED_CONSUMER_SHA256,
        guardrail.CUSTODY_CONTRACT_PATH: EXPECTED_CUSTODY_SHA256,
    }
    for path, sha256 in expected.items():
        assert path.read_bytes() == artifacts[path]
        assert hashlib.sha256(artifacts[path]).hexdigest() == sha256


def test_v1_binds_exact_source_authority_and_record_accounting() -> None:
    packet = _payload(guardrail.PACKET_PATH)
    anchors = packet["external_trust_anchors"]
    assert anchors["source_registry_size_bytes"] == 52_340_650
    assert anchors["source_registry_sha256"] == guardrail.REGISTRY_SHA256
    assert anchors["source_registry_git_blob"] == guardrail.REGISTRY_GIT_BLOB
    assert anchors["current_authoritative_surfaces_sha256"] == (
        "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248"
    )
    assert anchors["current_authoritative_surfaces_git_blob"] == (
        "d46c5fb1966dcefc6b923776b7d94c4f5009b889"
    )
    assert anchors["candidate_owned_expected_hashes_trusted"] is False
    accounting = packet["record_accounting"]
    assert accounting["root_field_record_count"] == 4_152
    assert accounting["workstream_record_count"] == 539
    assert accounting["total_record_count"] == 4_691
    assert len(accounting["full_record_identity_root_sha256"]) == 64
    identity = packet["record_identity_contract"]
    assert identity["digest"] == "FULL_SHA256_64_HEX_NO_TRUNCATION"
    assert identity["independent_of_shard_placement"] is True
    assert identity["independent_of_migrated_list_position"] is True


def test_v1_consumer_map_is_static_complete_only_with_runtime_trace_pending() -> None:
    source_map = _payload(guardrail.CONSUMER_MAP_PATH)
    assert source_map["consumer_count"] == 496
    assert source_map["discovery"]["literal_external_path_count"] == 493
    assert source_map["discovery"]["explicit_nonliteral_reader_count"] == 3
    assert source_map["discovery"]["literal_extension_counts"][".py"] == 467
    assert source_map["discovery"]["operation_counts"]["WRITER_AND_READER"] == 1
    assert source_map["boundary"] == {
        "consumer_migration_started": False,
        "runtime_coverage_complete": False,
        "static_inventory_claimed_as_runtime_complete": False,
    }
    assert all(value is False for value in source_map["required_shadow_evidence"].values())
    ids = [row["consumer_id"] for row in source_map["consumers"]]
    assert len(ids) == len(set(ids)) == 496
    paths = {row["path"] for row in source_map["consumers"]}
    assert set(guardrail.NONLITERAL_READERS).issubset(paths)


def test_v1_custody_contract_is_byte_exact_without_creating_payload() -> None:
    custody = _payload(guardrail.CUSTODY_CONTRACT_PATH)
    assert custody["compatibility_reconstruction"] == {
        "acceptance": "BYTE_IDENTICAL_TO_FROZEN_LEGACY_SOURCE",
        "decompressed_sha256": guardrail.REGISTRY_SHA256,
        "decompressed_size_bytes": 52_340_650,
        "semantic_reconstruction_alone_sufficient": False,
    }
    container = custody["container_contract"]
    assert container["algorithm"] == "RFC1952_GZIP_SINGLE_MEMBER_DEFLATE"
    assert container["forbid_concatenated_members"] is True
    assert container["forbid_trailing_bytes"] is True
    assert container["compressed_container_hash_is_normative_before_execution"] is False
    assert all(value is False for value in custody["boundary"].values())


def test_v1_projection_shard_api_and_source_mapping_contracts_are_strict() -> None:
    packet = _payload(guardrail.PACKET_PATH)
    projection = packet["current_projection_contract"]
    assert projection["maximum_bytes_exclusive"] == 1_048_576
    assert projection["additional_properties_allowed"] is False
    assert projection["recursive_additional_properties_allowed"] is False
    assert projection["source_mappings"]["active_blockers"]["include_statuses"] == [
        "blocked",
        "missing",
        "not_assessed",
        "partial",
    ]
    history = packet["canonical_history_contract"]
    assert history["maximum_uncompressed_shard_bytes"] == 5_242_880
    assert history["shard_closed_and_immutable_after_creation"] is True
    assert history["unique_shard_ids_and_paths"] is True
    api = packet["api_contract"]
    assert api["read_api"] == [
        "load_current_projection()",
        "get_current_target()",
        "get_current_maintenance_target()",
        "get_current_workstream(workstream_id)",
        "get_historical_record(record_id)",
        "iter_historical_records(...)",
        "verify_registry_integrity()",
        "reconstruct_legacy_registry()",
    ]
    assert api["integrity_verification_bypass_parameter_allowed"] is False
    assert api["write_contract"]["closed_history_mutation_api_exists"] is False


def test_v1_freezes_all_v0_regressions_and_unique_typed_controls() -> None:
    packet = _payload(guardrail.PACKET_PATH)
    controls = packet["negative_controls"]
    assert len(controls) == packet["negative_control_count"] == 52
    mutations = {row["mutation"] for row in controls}
    assert set(guardrail.V0_FALSE_ACCEPTANCES).issubset(mutations)
    assert sum(row["v0_false_acceptance_regression"] for row in controls) == 8
    error_codes = [row["expected_error_code"] for row in controls]
    assert len(error_codes) == len(set(error_codes))
    assert all(
        row["implementation_status"]
        == "REQUIRED_EXECUTION_REGRESSION_NOT_RUN_BY_PREPARATION"
        for row in controls
    )


def test_v1_authorizes_no_migration_cutover_or_authority_change() -> None:
    packet = _payload(guardrail.PACKET_PATH)
    assert packet["authorization"]["scientific_target"] == guardrail.SCIENTIFIC_TARGET
    assert packet["authorization"]["maintenance_target"] == guardrail.MAINTENANCE_TARGET
    assert packet["authorization"]["migration_execution_authorized"] is False
    assert all(value is False for value in packet["boundary"].values())
    forbidden = [
        "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
        "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    ]
    assert all(not (guardrail.REPO_ROOT / path).exists() for path in forbidden)


def test_v1_lean_certificate_binds_packet_and_nonauthorization() -> None:
    lean = (
        guardrail.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingGuardrailPacketV1.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_PACKET_SHA256 in lean
    assert EXPECTED_CONSUMER_SHA256 in lean
    assert EXPECTED_CUSTODY_SHA256 in lean
    assert guardrail.SCIENTIFIC_TARGET in lean
    assert guardrail.MAINTENANCE_TARGET in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean
    assert "productionProjectionGenerated : Bool := false" in lean
