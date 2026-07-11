from __future__ import annotations

import base64
import hashlib
import json
import subprocess
import sys
from typing import Any

from jsonschema import Draft202012Validator
from jsonschema.validators import validator_for

from formal.python.tools import (
    loop_control_registry_sharding_execution_readiness_packet_v3 as corrective,
)


EXPECTED_PACKET_SHA256 = "90037c92d74f4ab18be82863dd240065bc5ebd312e5b8647b52f1b3a549cb216"
EXPECTED_PROTOCOL_SHA256 = "ad65ceb56d3b284b3a55e433afc13745c3c574c9f2e7bf0fe367172924ea08e2"
EXPECTED_SCHEMA_SHA256 = "86289bf922d60c3320f040779a6043cdb3f2acf3d5393ce7503ef9d3375f6cde"
EXPECTED_HISTORY_RECORD_ID = (
    "lcr1:d75b26021e1590269867c3a4535d7069a6443f251600edd394983ad9e0c7fdcf"
)


def _payload(path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _copy(value: Any) -> Any:
    return json.loads(json.dumps(value))


def _assert_closed(node: Any) -> None:
    if isinstance(node, dict):
        if node.get("type") == "object":
            assert node.get("additionalProperties") is False
            assert set(node["required"]) == set(node["properties"])
        for value in node.values():
            _assert_closed(value)
    elif isinstance(node, list):
        for value in node:
            _assert_closed(value)


def test_corrective_v3_artifacts_are_deterministic() -> None:
    expected = {
        corrective.PACKET_PATH: EXPECTED_PACKET_SHA256,
        corrective.PROTOCOL_PATH: EXPECTED_PROTOCOL_SHA256,
        corrective.SCHEMA_PATH: EXPECTED_SCHEMA_SHA256,
    }
    artifacts = corrective.build_all()
    for path, expected_sha256 in expected.items():
        assert path.read_bytes() == artifacts[path]
        assert hashlib.sha256(artifacts[path]).hexdigest() == expected_sha256


def test_corrective_v3_cli_check_is_raw_checkout_portable_and_read_only() -> None:
    before = {path: path.read_bytes() for path in corrective.build_all()}
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.loop_control_registry_sharding_execution_readiness_packet_v3",
            "--check",
        ],
        cwd=corrective.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert {path: path.read_bytes() for path in before} == before


def test_v2_rejection_and_reviewed_inputs_remain_immutable() -> None:
    for path, expected in corrective.EXPECTED_SHA256.items():
        assert hashlib.sha256(corrective._git_blob(path)).hexdigest() == expected
    packet = _payload(corrective.PACKET_PATH)
    custody = packet["rejected_v2_custody"]
    assert custody["v2_execution_readiness_accepted"] is False
    assert custody["v2_preserved_as_historical_corrective_evidence"] is True
    assert custody["review_sha256"] == corrective.EXPECTED_SHA256[
        corrective.V2_REVIEW_REL
    ]


def test_all_ten_v3_schemas_pass_metaschema_and_recursive_closure() -> None:
    bundle = _payload(corrective.SCHEMA_PATH)
    assert bundle["schema_count"] == len(bundle["schemas"]) == 10
    for schema in bundle["schemas"].values():
        validator_for(schema).check_schema(schema)
        _assert_closed(schema)
        assert "/readiness-v3/" in schema["$id"]


def test_repository_and_prototype_path_profiles_are_context_specific() -> None:
    bundle = _payload(corrective.SCHEMA_PATH)
    schemas = bundle["schemas"]
    repository_schema = schemas["consumer_source_map"]["properties"]["consumers"][
        "items"
    ]["properties"]["path"]
    repository = Draft202012Validator(repository_schema)
    source_map = json.loads(corrective._git_blob(corrective.CONSUMER_MAP_REL))
    paths = [row["path"] for row in source_map["consumers"]]
    assert len(paths) == 496
    assert all(repository.is_valid(path) for path in paths)
    for required in [".gitattributes", ".vscode/settings.json", "Physics Imps and Sigs.txt"]:
        assert required in paths and repository.is_valid(required)

    prototype_schema = schemas["validation_report"]["oneOf"][1]["properties"][
        "issues"
    ]["items"]["oneOf"][0]["properties"]["artifact_path"]
    prototype = Draft202012Validator(prototype_schema)
    assert prototype.is_valid("validation/report.json")
    for invalid in [
        "/absolute/report.json",
        "//server/share/report.json",
        ".hidden/report.json",
        "path with spaces/report.json",
        "../report.json",
        "a\\report.json",
    ]:
        assert not prototype.is_valid(invalid), invalid


def test_semantic_field_profile_map_is_exhaustive_and_declared() -> None:
    bundle = _payload(corrective.SCHEMA_PATH)
    mapping = bundle["field_path_profile_map"]
    expected_keys = {
        "compatibility_reconstruction_result./properties/custody_payload_identity/properties/path",
        "compatibility_reconstruction_result./properties/reconstruction_identity/properties/path",
        "compatibility_reconstruction_result./properties/source_identity/properties/path",
        "compatibility_reconstruction_result./properties/validator_identity/properties/path",
        "consumer_source_map./properties/baseline/properties/path",
        "consumer_source_map./properties/consumers/items/properties/path",
        "current_projection./properties/active_blockers/items/properties/evidence_pointer",
        "current_projection./properties/active_scientific_workstream/properties/original_json_pointer",
        "current_projection./properties/current_artifacts/items/properties/path",
        "current_projection./properties/history_index_pointer/properties/path",
        "current_projection./properties/maintenance_authority/properties/evidence/properties/path",
        "current_projection./properties/source_legacy_identity/properties/path",
        "history_index./properties/consumer_source_map_pointer/properties/path",
        "history_index./properties/custody_manifest_pointer/properties/path",
        "history_index./properties/shards/items/properties/path",
        "history_index./properties/source_registry_identity/properties/path",
        "history_shard_record./properties/original_json_pointer",
        "history_shard_record./properties/source_path",
        "legacy_byte_custody_manifest./properties/contract_pointer/properties/path",
        "legacy_byte_custody_manifest./properties/generation_provenance/properties/run_id",
        "legacy_byte_custody_manifest./properties/gzip_profile/properties/path",
        "legacy_byte_custody_manifest./properties/payload_identity/properties/path",
        "legacy_byte_custody_manifest./properties/source_identity/properties/path",
        "runtime_shadow_trace_event./properties/consumer_path",
        "runtime_shadow_trace_event./properties/fields_accessed/items",
        "runtime_shadow_trace_event./properties/resolved_registry_paths/properties/candidate_prototype_path",
        "runtime_shadow_trace_event./properties/resolved_registry_paths/properties/legacy_repository_path",
        "runtime_shadow_trace_event./properties/run_id",
        "runtime_shadow_trace_event./properties/write_paths/items",
        "runtime_shadow_trace_manifest./properties/run_id",
        "validation_report./oneOf/*/properties/issues/items/oneOf/*/properties/artifact_path",
        "validation_report./oneOf/*/properties/issues/items/oneOf/*/properties/json_pointer",
    }
    # One extra key is the current scientific report path; keep it explicit.
    expected_keys.add(
        "current_projection./properties/active_scientific_workstream/properties/report"
    )
    assert set(mapping) == expected_keys
    assert len(mapping) == 33
    assert not (set(mapping.values()) - set(bundle["path_profiles"]))
    assert mapping[
        "history_index./properties/shards/items/properties/path"
    ] == "PROTOTYPE_SHARD_RELPATH"
    assert mapping[
        "runtime_shadow_trace_event./properties/write_paths/items"
    ] == "CONTEXT_TAGGED_REPOSITORY_OR_PROTOTYPE_RELPATH"
    contract = bundle["field_path_profile_map_contract"]
    assert contract["mapping_count"] == 33
    assert contract["undefined_profile_count"] == 0
    assert contract["mapping_sha256"] == hashlib.sha256(
        corrective.compact_json_bytes(mapping)
    ).hexdigest()


def test_json_pointer_run_id_and_shard_filename_contracts_are_executable() -> None:
    schemas = _payload(corrective.SCHEMA_PATH)["schemas"]
    pointer_schemas = [
        schemas["current_projection"]["properties"]["active_scientific_workstream"][
            "properties"
        ]["original_json_pointer"],
        schemas["history_shard_record"]["properties"]["original_json_pointer"],
        schemas["runtime_shadow_trace_event"]["properties"]["fields_accessed"][
            "items"
        ],
        schemas["validation_report"]["oneOf"][1]["properties"]["issues"][
            "items"
        ]["oneOf"][0]["properties"]["json_pointer"],
    ]
    for pointer_schema in pointer_schemas:
        validator = Draft202012Validator(pointer_schema)
        assert validator.is_valid("")
        assert validator.is_valid("/a~1b/~0")
        assert not validator.is_valid("relative")
        assert not validator.is_valid("/bad~2escape")

    run_schemas = [
        schemas["legacy_byte_custody_manifest"]["properties"][
            "generation_provenance"
        ]["properties"]["run_id"],
        schemas["runtime_shadow_trace_event"]["properties"]["run_id"],
        schemas["runtime_shadow_trace_manifest"]["properties"]["run_id"],
    ]
    assert len({json.dumps(schema, sort_keys=True) for schema in run_schemas}) == 1
    run_validator = Draft202012Validator(run_schemas[0])
    assert run_validator.is_valid("run-20260711_01")
    assert not run_validator.is_valid(".hidden")
    assert not run_validator.is_valid("x" * 65)

    shard_path = schemas["history_index"]["properties"]["shards"]["items"][
        "properties"
    ]["path"]
    shard_validator = Draft202012Validator(shard_path)
    assert shard_validator.is_valid("history/shards/LOOP_CONTROL_HISTORY_0001.jsonl")
    assert not shard_validator.is_valid("history/shards/arbitrary.jsonl")
    assert not shard_validator.is_valid("other/LOOP_CONTROL_HISTORY_0001.jsonl")
    assert not shard_validator.is_valid("../LOOP_CONTROL_HISTORY_0001.jsonl")


def test_exact_control_error_map_is_shared_and_fails_closed() -> None:
    protocol = _payload(corrective.PROTOCOL_PATH)
    mapping = protocol["control_error_map"]
    assert len(mapping) == 60
    assert protocol["control_error_map_sha256"] == hashlib.sha256(
        corrective.compact_json_bytes(mapping)
    ).hexdigest()
    issue_schema = protocol["production_validator_interface"]["error_result"]
    issue_validator = Draft202012Validator(issue_schema)
    for control_id, error_code in mapping.items():
        issue = {
            "artifact_path": "validation/report.json",
            "control_id": control_id,
            "error_code": error_code,
            "json_pointer": "",
            "message": "exact mapping probe",
        }
        assert issue_validator.is_valid(issue), control_id
        wrong = _copy(issue)
        wrong["error_code"] = "V1-E-WRONG"
        assert not issue_validator.is_valid(wrong), control_id
    for invalid_id in [
        "REGISTRY-V1-NC-000",
        "REGISTRY-V1-NC-999",
        "REGISTRY-READINESS-V1-RC-999",
    ]:
        assert not issue_validator.is_valid(
            {
                "artifact_path": "validation/report.json",
                "control_id": invalid_id,
                "error_code": "V1-E-WRONG",
                "json_pointer": "",
                "message": "unknown control",
            }
        )
    assert issue_validator.is_valid(
        {
            "artifact_path": "validation/report.json",
            "control_id": None,
            "error_code": "V1-E-NONCONTROL-DIAGNOSTIC",
            "json_pointer": "",
            "message": "non-control diagnostic",
        }
    )
    report_schema = _payload(corrective.SCHEMA_PATH)["schemas"]["validation_report"]
    for branch in report_schema["oneOf"]:
        issues = branch["properties"]["issues"]
        if issues.get("minItems") == 1:
            assert issues["items"] == issue_schema


def test_positive_fixtures_have_real_builders_hashes_and_artifact_validation() -> None:
    protocol = _payload(corrective.PROTOCOL_PATH)
    contracts = protocol["typed_control_harness"]["positive_fixture_contracts"]
    schemas = _payload(corrective.SCHEMA_PATH)["schemas"]
    assert len(contracts) == 5
    for fixture_id, contract in contracts.items():
        builder = getattr(corrective, contract["builder_entrypoint"])
        payload = builder(**contract["builder_args"])
        assert payload == contract["fixture_payload"]
        assert corrective.validate_preparation_fixture_v3(fixture_id, payload)
        assert Draft202012Validator(schemas[contract["schema_name"]]).is_valid(payload)
        assert hashlib.sha256(corrective.canonical_json_bytes(payload)).hexdigest() == (
            contract["canonical_fixture_sha256"]
        )
        assert contract["embedded_fixture_only_not_a_complete_candidate"] is True
        assert contract["full_profile_baseline_executed"] is False
        assert contract[
            "full_profile_baseline_must_pass_before_mutation_at_execution"
        ] is True
        assert contract["artifact_contract_validator_args"]
        assert contract["identity_posture"] in {
            "FROZEN_REVIEWED_SOURCE_MEMBERSHIP_IDENTITY",
            "SYNTHETIC_PREPARATION_FIXTURE_CANDIDATE_IDENTITY_NOT_A_PRODUCTION_TRUST_ANCHOR",
            "SYNTHETIC_PREPARATION_FIXTURE_IDENTITIES_NOT_PRODUCTION_TRUST_ANCHORS",
        }

    history = contracts["VALID_HISTORY_PAYLOAD_SOURCE_STRING_v3"]
    row = history["fixture_payload"]
    assert row["logical_key"] == "selected"
    assert row["original_json_pointer"] == "/selected"
    assert row["record_id"] == EXPECTED_HISTORY_RECORD_ID
    assert row["payload_canonical_json_utf8_base64"] == "Im5vIg=="
    assert base64.b64decode(row["payload_canonical_json_utf8_base64"]) == b'"no"'
    assert history["frozen_source_membership"]["source_git_blob"] == (
        corrective.REGISTRY_GIT_BLOB
    )


def test_all_eight_regressions_are_atomic_artifact_contracts() -> None:
    protocol = _payload(corrective.PROTOCOL_PATH)
    harness = protocol["typed_control_harness"]
    rows = harness["readiness_regressions"]
    fixtures = harness["positive_fixture_contracts"]
    assert len(rows) == harness["readiness_regression_control_count"] == 8
    assert harness["readiness_regression_atomic_case_count"] == 8
    assert [row["control_sequence"] for row in rows] == list(range(1, 9))
    assert all(len(row["mutation_matrix"]) == 1 for row in rows)
    assert all(len(row["expected_exact_error_set"]) == 1 for row in rows)
    for row in rows:
        fixture_id = row["positive_fixture_id"]
        contract = fixtures[fixture_id]
        assert "_v2" not in row["mutation_precondition"]
        assert fixture_id in row["mutation_precondition"]
        assert row["validator_entrypoint"] == contract[
            "artifact_contract_validator_entrypoint"
        ]
        assert row["positive_artifact_validator_entrypoint"] == row[
            "validator_entrypoint"
        ]
        assert row["positive_artifact_validator_args"] == contract[
            "artifact_contract_validator_args"
        ]
        assert row["full_candidate_profile_assignment"] == row["validator_profile"]
        invocation = harness["full_profile_execution_context_derivation"][
            "profile_invocations"
        ][row["validator_profile"]]
        assert row["full_candidate_profile_entrypoint"] == invocation["entrypoint"]
        assert row["full_candidate_profile_entrypoint"] in row[
            "full_candidate_profile_args_derivation"
        ] or row["validator_profile"] in row["full_candidate_profile_args_derivation"]
        assert row[
            "preparation_does_not_claim_full_profile_baseline_execution"
        ] is True
        assert row["production_artifact_validator_implemented_or_executed"] is False
    assert set(
        protocol["production_validator_interface"][
            "artifact_contract_validator_entrypoints"
        ]
    ) == {"control_harness_report", "history_shard_record", "validation_report"}
    derivation = harness["full_profile_execution_context_derivation"]
    assert derivation["realized_full_profile_baselines_executed"] is False
    assert derivation["realized_values_may_not_be_selected_by_candidate_metadata"] is True
    assert set(derivation["profile_invocations"]) == {
        "CUTOVER_ELIGIBILITY",
        "PROTOTYPE_INTEGRITY",
        "SHADOW_PARITY",
        "WRITE_SAFETY",
    }


def test_eight_mutations_isolate_their_intended_decisions() -> None:
    protocol = _payload(corrective.PROTOCOL_PATH)
    rows = {
        row["control_id"]: row
        for row in protocol["typed_control_harness"]["readiness_regressions"]
    }
    fixtures = protocol["typed_control_harness"]["positive_fixture_contracts"]
    schemas = _payload(corrective.SCHEMA_PATH)["schemas"]

    report_validator = Draft202012Validator(schemas["validation_report"])
    cutover = _copy(fixtures["VALID_CUTOVER_REPORT_v3"]["fixture_payload"])
    assert report_validator.is_valid(cutover)
    cutover["executed_profile_closure"] = rows[
        "REGISTRY-READINESS-V1-RC-001"
    ]["mutation_matrix"][0]["after"]
    assert not report_validator.is_valid(cutover)

    history = fixtures["VALID_HISTORY_PAYLOAD_SOURCE_STRING_v3"]["fixture_payload"]
    rc2 = rows["REGISTRY-READINESS-V1-RC-002"]["mutation_matrix"][0]
    before = base64.b64decode(rc2["before"], validate=True)
    after = base64.b64decode(rc2["after"], validate=True)
    assert before == after == b'"no"'
    assert base64.b64encode(after).decode("ascii") != rc2["after"]
    assert history["payload_canonical_json_utf8_base64"] == rc2["before"]
    assert rows["REGISTRY-READINESS-V1-RC-003"]["mutation_matrix"][0][
        "before"
    ] == history["payload_size_bytes"] == 4
    rc4 = rows["REGISTRY-READINESS-V1-RC-004"]["mutation_matrix"][0]
    rc4_bytes = base64.b64decode(rc4["after"], validate=True)
    assert json.loads(rc4_bytes) == "no"
    assert corrective.compact_json_bytes(json.loads(rc4_bytes)) != rc4_bytes

    failed = fixtures["VALID_FAILED_REPORT_v3"]["fixture_payload"]
    for control_id in ["REGISTRY-READINESS-V1-RC-005", "REGISTRY-READINESS-V1-RC-006"]:
        mutated = _copy(failed)
        mutated["issues"][0]["artifact_path"] = rows[control_id]["mutation_matrix"][0][
            "after"
        ]
        assert not report_validator.is_valid(mutated)

    passed = _copy(fixtures["VALID_PASSED_REPORT_v3"]["fixture_payload"])
    rc7_issue = rows["REGISTRY-READINESS-V1-RC-007"]["mutation_matrix"][0][
        "after"
    ][0]
    assert Draft202012Validator(
        protocol["production_validator_interface"]["error_result"]
    ).is_valid(rc7_issue)
    passed["issues"] = [rc7_issue]
    assert not report_validator.is_valid(passed)

    harness = _copy(fixtures["VALID_HARNESS_SUCCESS_v3"]["fixture_payload"])
    harness_validator = Draft202012Validator(schemas["control_harness_report"])
    assert harness_validator.is_valid(harness)
    rc8 = rows["REGISTRY-READINESS-V1-RC-008"]["mutation_matrix"][0]
    harness["base_candidate_sha256_after"] = rc8["after"]
    assert harness_validator.is_valid(harness)
    assert harness["base_candidate_sha256_before"] != harness[
        "base_candidate_sha256_after"
    ]
    assert "BASE_CANDIDATE_SHA256_BEFORE_EQUALS_AFTER" in protocol[
        "success_report_invariants"
    ]["control_harness_report"]


def test_runtime_trace_paths_are_split_typed_and_run_bound() -> None:
    bundle = _payload(corrective.SCHEMA_PATH)
    schema = bundle["schemas"]["runtime_shadow_trace_event"]
    validator = Draft202012Validator(schema)
    event = {
        "access_granularity": "EXACT_FIELDS",
        "candidate_result_sha256": "a" * 64,
        "comparison_mode": "CANONICAL_TYPED_ENVELOPE",
        "consumer_id": "lcc1:" + "b" * 64,
        "consumer_path": ".gitattributes",
        "consumer_source_sha256": "c" * 64,
        "fields_accessed": ["/current_projection_v0"],
        "legacy_result_sha256": "a" * 64,
        "operation_id": "get-current-target",
        "operation_type": "GET_CURRENT_TARGET",
        "resolved_registry_paths": {
            "candidate_prototype_path": "projection/LOOP_CONTROL_CURRENT_v1.prototype.json",
            "legacy_repository_path": corrective.REGISTRY_PATH,
        },
        "run_id": "run-20260711",
        "runtime_entrypoint": "shadow_get_current_target",
        "semantic_parity": True,
        "source_commit": corrective.SOURCE_COMMIT,
        "trace_id": "lct1:" + "d" * 64,
        "trace_schema_id": "LOOP_CONTROL_SHADOW_TRACE_EVENT_v3",
        "write_attempted": False,
        "write_paths": [],
    }
    assert validator.is_valid(event)
    wrong_context = _copy(event)
    wrong_context["resolved_registry_paths"]["candidate_prototype_path"] = ".gitattributes"
    assert not validator.is_valid(wrong_context)
    write = _copy(event)
    write["write_attempted"] = True
    write["write_paths"] = [
        {"path": ".gitattributes", "path_context": "REPOSITORY_RELPATH"}
    ]
    assert validator.is_valid(write)
    write["write_paths"][0]["path_context"] = "PROTOTYPE_ARTIFACT_RELPATH"
    assert not validator.is_valid(write)

    shadow = _payload(corrective.PROTOCOL_PATH)["runtime_shadow_tracing_protocol"]
    assert "<run_id>" not in shadow["trace_output"]
    assert shadow["trace_output_is_relative_to_validated_run_root"] is True
    assert shadow["trace_output"] == (
        "traces/LOOP_CONTROL_RUNTIME_SHADOW_TRACE_v1.jsonl"
    )


def test_record_root_algorithms_and_shadow_nonmigration_attestations_remain() -> None:
    protocol = _payload(corrective.PROTOCOL_PATH)
    payload = protocol["history_payload_validation_algorithm"]
    assert payload["record_id_domain_value"] == "LOOP_CONTROL_RECORD_ID_v1"
    assert payload["record_id_preimage_serializer"] == (
        "HISTORY_PAYLOAD_COMPACT_JSON_v1_UTF8_NO_TERMINAL_LF"
    )
    assert payload["record_id_result"] == (
        "lcr1:PLUS_LOWERCASE_SHA256_HEX_OF_PREIMAGE_BYTES"
    )
    assert payload["full_record_identity_root_algorithm"].endswith(
        "JOIN_UTF8_LF_NO_TERMINAL_LF_SHA256"
    )
    shadow = _payload(corrective.SCHEMA_PATH)["schemas"][
        "runtime_shadow_trace_manifest"
    ]
    assert shadow["properties"]["consumer_migration_performed"]["const"] is False
    assert shadow["properties"]["cutover_performed"]["const"] is False


def test_v3_preserves_nonauthorization_and_historical_path_absence() -> None:
    packet = _payload(corrective.PACKET_PATH)
    assert packet["authorization"]["scientific_target"] == corrective.SCIENTIFIC_TARGET
    assert packet["authorization"]["maintenance_target"] == corrective.MAINTENANCE_TARGET
    assert packet["authorization"]["packet_target_is_current_maintenance_authority"] is False
    assert packet["authorization"]["prototype_execution_target_selected"] is False
    assert packet["authorization"]["registry_migration_execution_authorized"] is False
    assert packet["authorization"]["registry_cutover_authorized"] is False
    assert all(value is False for value in packet["boundary"].values())
    assert all(
        value is False
        for key, value in packet["selection_posture"].items()
        if key.endswith("selectable")
    )
    for path in corrective.FORBIDDEN_PATHS:
        assert not corrective._path_exists_at_source_commit(path)


def test_v3_lean_certificate_binds_artifacts_and_nonauthorization() -> None:
    lean = (
        corrective.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingExecutionReadinessPacketV3.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_PACKET_SHA256 in lean
    assert EXPECTED_PROTOCOL_SHA256 in lean
    assert EXPECTED_SCHEMA_SHA256 in lean
    assert corrective.EXPECTED_SHA256[corrective.V2_REVIEW_REL] in lean
    assert corrective.SCIENTIFIC_TARGET in lean
    assert corrective.MAINTENANCE_TARGET in lean
    assert "correctiveV3IndependentReviewRequired : Bool := true" in lean
    assert "prototypeExecutionSelected : Bool := false" in lean
    assert "migrationExecutionAuthorized : Bool := false" in lean
    assert "registryCutoverAuthorized : Bool := false" in lean
