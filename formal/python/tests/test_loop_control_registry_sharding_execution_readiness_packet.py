from __future__ import annotations

import hashlib
import json
import subprocess
from typing import Any

from formal.python.tools import (
    loop_control_registry_sharding_execution_readiness_packet as readiness,
)


EXPECTED_PACKET_SHA256 = "ddca270745ebea3659cf9b53aa09c4c0c25a0983101a1d310e1f98380b3874c8"
EXPECTED_SCHEMA_SHA256 = "24f1f2703d9c6c2510b314d132bfdfc09ab9f6207d209bc2620eed328e176a58"
EXPECTED_PROTOCOL_SHA256 = "90a609f6d2be11be94b8c03ea04b1d58452a6f9b9fa26d227383fbfece195c8e"


def _payload(path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _assert_recursively_closed_schema(node: Any) -> None:
    if isinstance(node, dict):
        if node.get("type") == "object":
            assert node.get("additionalProperties") is False
            assert set(node.get("required", [])) == set(node.get("properties", {}))
        for value in node.values():
            _assert_recursively_closed_schema(value)
    elif isinstance(node, list):
        for value in node:
            _assert_recursively_closed_schema(value)


def test_readiness_artifacts_are_deterministic_from_accepted_commit() -> None:
    artifacts = readiness.build_all()
    expected = {
        readiness.PACKET_PATH: EXPECTED_PACKET_SHA256,
        readiness.SCHEMA_BUNDLE_PATH: EXPECTED_SCHEMA_SHA256,
        readiness.PROTOCOL_BUNDLE_PATH: EXPECTED_PROTOCOL_SHA256,
    }
    assert set(artifacts) == set(expected)
    for path, sha256 in expected.items():
        assert path.read_bytes() == artifacts[path]
        assert hashlib.sha256(artifacts[path]).hexdigest() == sha256


def test_readiness_cli_check_is_read_only_and_passes() -> None:
    before = {path: path.read_bytes() for path in readiness.build_all()}
    result = subprocess.run(
        [
            str(readiness.REPO_ROOT / ".venv/Scripts/python.exe"),
            "-m",
            "formal.python.tools.loop_control_registry_sharding_execution_readiness_packet",
            "--check",
        ],
        cwd=readiness.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert {path: path.read_bytes() for path in before} == before


def test_packet_binds_accepted_v1_evidence_and_current_targets() -> None:
    packet = _payload(readiness.PACKET_PATH)
    accepted = packet["accepted_v1_input"]
    assert accepted == {
        "consumer_count": 496,
        "control_count": 52,
        "guardrail_packet_sha256": readiness.EXPECTED_SHA256[readiness.V1_PACKET_REL],
        "guardrail_review_sha256": readiness.EXPECTED_SHA256[readiness.V1_REVIEW_REL],
        "migration_execution_readiness_accepted": False,
        "open_finding_count": 4,
        "record_count": 4_691,
    }
    authorization = packet["authorization"]
    assert authorization["scientific_target"] == readiness.SCIENTIFIC_TARGET
    assert authorization["maintenance_target"] == readiness.MAINTENANCE_TARGET
    assert authorization["packet_target_is_current_maintenance_authority"] is False
    assert authorization["prototype_execution_target_selected"] is False
    assert authorization["registry_migration_execution_authorized"] is False
    assert authorization["review_target_recommended_not_selected"] == readiness.REVIEW_TARGET


def test_ten_machine_readable_schemas_are_exact_and_recursively_closed() -> None:
    bundle = _payload(readiness.SCHEMA_BUNDLE_PATH)
    assert bundle["draft"] == "JSON_SCHEMA_2020_12"
    assert bundle["schema_count"] == len(bundle["schemas"]) == 10
    assert set(bundle["schemas"]) == {
        "compatibility_reconstruction_result",
        "control_harness_report",
        "consumer_source_map",
        "current_projection",
        "history_index",
        "history_shard_record",
        "legacy_byte_custody_manifest",
        "runtime_shadow_trace_event",
        "runtime_shadow_trace_manifest",
        "validation_report",
    }
    assert bundle["canonical_instance_bytes"] == {
        "allow_nan": False,
        "duplicate_keys_rejected_before_schema_evaluation": True,
        "encoding": "UTF-8_NO_BOM",
        "final_newline": "EXACTLY_ONE_LF",
        "key_order": "LEXICOGRAPHIC",
        "line_endings": "LF_ONLY",
        "unknown_fields_rejected": True,
    }
    for schema in bundle["schemas"].values():
        assert schema["$schema"] == "https://json-schema.org/draft/2020-12/schema"
        _assert_recursively_closed_schema(schema)


def test_projection_schema_is_structural_while_external_values_preserve_authority() -> None:
    projection = _payload(readiness.SCHEMA_BUNDLE_PATH)["schemas"]["current_projection"]
    props = projection["properties"]
    assert props["status"]["const"] == "SHADOW_PROTOTYPE_NONAUTHORITATIVE"
    constraints = _payload(readiness.SCHEMA_BUNDLE_PATH)["external_value_constraints"]
    assert constraints["current_projection./scientific_authority/current_target"] == readiness.SCIENTIFIC_TARGET
    assert constraints["current_projection./maintenance_authority/current_maintenance_target"] == readiness.MAINTENANCE_TARGET
    assert constraints["current_projection./scientific_authority/authority_commitment_sha256"] == readiness.AUTHORITY_COMMITMENT_SHA256
    nonpromotion = props["nonpromotion_assertions"]["properties"]
    assert len(nonpromotion) == 8
    assert all(row == {"enum": ["no", "yes"], "type": "string"} for row in nonpromotion.values())
    assert constraints["current_projection./nonpromotion_assertions/*"] == "no"
    assert props["history_index_pointer"]["properties"]["schema_id"]["const"] == (
        "LOOP_CONTROL_HISTORY_INDEX_v1"
    )


def test_validator_contract_is_external_fail_closed_and_dependency_locked_before_use() -> None:
    protocol = _payload(readiness.PROTOCOL_BUNDLE_PATH)
    interface = protocol["production_validator_interface"]
    assert interface["read_only"] is True
    assert interface["write_interfaces_separate"] is True
    assert interface["integrity_bypass_parameter_allowed"] is False
    assert interface["candidate_expected_values_are_authoritative"] is False
    assert len(interface["frozen_functions"]) == 9
    assert len(interface["profile_specific_entrypoints"]) == 4
    assert interface["profile_selected_by_caller_not_candidate"] is True
    lock = protocol["validator_engine_and_lock_contract"]
    assert lock == {
        "direct_requirements_lock_entry_present_at_source_commit": False,
        "duplicate_key_and_nonfinite_checks_are_parser_level_not_schema_only": True,
        "engine": "jsonschema",
        "implementation_blocked_until_direct_lock_and_transitive_closure_reviewed": True,
        "required_draft": "2020-12",
        "required_exact_version": "4.26.0",
        "requirements_path": "requirements.ci.lock",
    }


def test_all_52_controls_freeze_isolated_exact_error_decisions_without_execution() -> None:
    harness = _payload(readiness.PROTOCOL_BUNDLE_PATH)["typed_control_harness"]
    controls = harness["controls"]
    assert harness["control_count"] == len(controls) == 52
    assert harness["production_validator_exists"] is False
    assert harness["execution_complete"] is False
    assert len({row["control_id"] for row in controls}) == 52
    expected_codes = [row["expected_exact_error_set"][0] for row in controls]
    assert len(set(expected_codes)) == 52
    assert sum(row["v0_false_acceptance_regression"] for row in controls) == 8
    assert all(row["execution_status"] == "NOT_EXECUTED_PREPARATION_ONLY" for row in controls)
    assert all(row["baseline_candidate_recreated_before_mutation"] for row in controls)
    assert all(row["subsequent_controls_receive_unmodified_baseline"] for row in controls)
    assert all(len(row["expected_exact_error_set"]) == 1 for row in controls)
    by_id = {row["control_id"]: row for row in controls}
    assert by_id["REGISTRY-V1-NC-041"]["validator_profile"] == "WRITE_SAFETY"
    assert by_id["REGISTRY-V1-NC-042"]["validator_profile"] == "WRITE_SAFETY"
    assert by_id["REGISTRY-V1-NC-044"]["validator_profile"] == "CUTOVER_ELIGIBILITY"
    assert by_id["REGISTRY-V1-NC-045"]["validator_profile"] == "SHADOW_PARITY"
    assert by_id["REGISTRY-V1-NC-046"]["validator_profile"] == "SHADOW_PARITY"
    profiles = harness["validator_profiles"]
    assert profiles["SHADOW_PARITY"]["legacy_monolith_readers_required"] is True
    assert profiles["CUTOVER_ELIGIBILITY"]["legacy_monolith_readers_required"] is False
    assert harness["profile_is_caller_selected_never_candidate_selected"] is True


def test_shadow_protocol_requires_disposition_and_parity_for_all_consumers() -> None:
    shadow = _payload(readiness.PROTOCOL_BUNDLE_PATH)["runtime_shadow_tracing_protocol"]
    assert shadow["all_496_static_rows_require_final_disposition"] is True
    assert shadow["consumer_migration_or_cutover_during_trace"] is False
    assert shadow["comparison"] == (
        "LEGACY_AND_NEW_READ_EXECUTED_FOR_SAME_OPERATION_AND_INPUT"
    )
    assert "EVERY_RUNTIME_TRACE_REQUIRED_ROW_OBSERVED" in shadow["coverage_acceptance"]
    assert "ZERO_SEMANTIC_PARITY_MISMATCHES" in shadow["coverage_acceptance"]
    trace_schema = _payload(readiness.SCHEMA_BUNDLE_PATH)["schemas"]["runtime_shadow_trace_event"]
    assert set(shadow["required_trace_fields"]) == set(trace_schema["required"])


def test_byte_custody_requires_exact_detached_reconstruction_without_creating_payload() -> None:
    protocol = _payload(readiness.PROTOCOL_BUNDLE_PATH)
    custody = protocol["byte_custody_execution_procedure"]
    assert custody["semantic_equivalence_alone_sufficient"] is False
    assert custody["acceptance"] == {
        "byte_identical": True,
        "decompressed_sha256": readiness.EXPECTED_SHA256[readiness.REGISTRY_REL],
        "decompressed_size_bytes": 52_340_650,
        "detached_clean_checkout_required": True,
        "reconstructed_sha256": readiness.EXPECTED_SHA256[readiness.REGISTRY_REL],
    }
    assert protocol["authorization"]["custody_payload_creation_authorized_now"] is False
    assert all(path.startswith(readiness.PROTOTYPE_ROOT) for path in protocol["prototype_paths"].values())


def test_failure_rollback_is_scoped_and_cannot_move_authority() -> None:
    rollback = _payload(readiness.PROTOCOL_BUNDLE_PATH)["failure_and_rollback"]
    assert rollback["rollback_scope"] == (
        "DELETE_ONLY_FILES_CREATED_UNDER_THE_EXACT_RUN_ID_PROTOTYPE_ROOT"
    )
    assert rollback["rollback_requires_verified_resolved_path_under_prototype_root"] is True
    assert rollback["rollback_uses_git_history_rewrite"] is False
    assert rollback["failure_may_rotate_target_or_authority"] is False
    assert rollback["failure_may_touch_legacy_monolith"] is False
    assert rollback["failure_may_touch_scientific_artifacts"] is False


def test_packet_is_preparation_only_and_production_paths_remain_absent() -> None:
    packet = _payload(readiness.PACKET_PATH)
    assert len(packet["preparation_obligations_frozen"]) == 8
    assert len(packet["migration_execution_selection_conditions"]) == 10
    assert all(value is False for value in packet["boundary"].values())
    for value in _payload(readiness.PROTOCOL_BUNDLE_PATH)["authorization"].values():
        assert value is False
    for relative in readiness.FORBIDDEN_PRODUCTION_PATHS:
        assert not (readiness.REPO_ROOT / relative).exists()


def test_lean_certificate_binds_all_three_artifacts_and_nonauthorization() -> None:
    lean = (
        readiness.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingExecutionReadinessPacket.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_PACKET_SHA256 in lean
    assert EXPECTED_SCHEMA_SHA256 in lean
    assert EXPECTED_PROTOCOL_SHA256 in lean
    assert readiness.SCIENTIFIC_TARGET in lean
    assert readiness.MAINTENANCE_TARGET in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean
    assert "prototypeArtifactsCreated : Bool := false" in lean
    assert "unitLedgerExecuted : Bool := false" in lean
