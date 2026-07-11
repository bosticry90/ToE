from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from typing import Any

from jsonschema import Draft202012Validator
from jsonschema.validators import validator_for

from formal.python.tools import (
    loop_control_registry_sharding_execution_readiness_packet_v2 as corrective,
)


EXPECTED_PACKET_SHA256 = "7b266614ef80b28595bf617110a18b5853f0171d591d2f43fd2ef06759d82f76"
EXPECTED_PROTOCOL_SHA256 = "38f484e16d3fb87fcfe99df4cd92a66d538ff748d8abc9e78d8600955a480e22"
EXPECTED_SCHEMA_SHA256 = "68dc9a1a3ab9489e84dea59be3b92db1cd0fdc8bc8185338adea007998edb03f"


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


def test_corrective_v2_artifacts_are_deterministic() -> None:
    expected = {
        corrective.PACKET_PATH: EXPECTED_PACKET_SHA256,
        corrective.PROTOCOL_PATH: EXPECTED_PROTOCOL_SHA256,
        corrective.SCHEMA_PATH: EXPECTED_SCHEMA_SHA256,
    }
    artifacts = corrective.build_all()
    for path, sha256 in expected.items():
        assert path.read_bytes() == artifacts[path]
        assert hashlib.sha256(artifacts[path]).hexdigest() == sha256


def test_corrective_v2_cli_check_is_raw_checkout_portable_and_read_only() -> None:
    before = {path: path.read_bytes() for path in corrective.build_all()}
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.loop_control_registry_sharding_execution_readiness_packet_v2",
            "--check",
        ],
        cwd=corrective.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert {path: path.read_bytes() for path in before} == before


def test_v1_rejection_and_v1_artifacts_remain_immutable() -> None:
    for path, expected in corrective.EXPECTED_SHA256.items():
        assert hashlib.sha256(corrective._git_blob(path)).hexdigest() == expected
    packet = _payload(corrective.PACKET_PATH)
    custody = packet["rejected_v1_custody"]
    assert custody["v1_execution_readiness_accepted"] is False
    assert custody["v1_preserved_as_historical_corrective_evidence"] is True
    assert custody["review_sha256"] == corrective.EXPECTED_SHA256[corrective.V1_REVIEW_REL]


def test_all_ten_v2_schemas_pass_metaschema_and_recursive_closure() -> None:
    bundle = _payload(corrective.SCHEMA_PATH)
    assert bundle["schema_count"] == len(bundle["schemas"]) == 10
    for schema in bundle["schemas"].values():
        validator_for(schema).check_schema(schema)
        _assert_closed(schema)
        assert "/readiness-v2/" in schema["$id"]


def test_repository_path_profile_round_trips_all_496_frozen_consumers() -> None:
    schemas = _payload(corrective.SCHEMA_PATH)["schemas"]
    path_schema = schemas["consumer_source_map"]["properties"]["consumers"][
        "items"
    ]["properties"]["path"]
    validator = Draft202012Validator(path_schema)
    source_map = json.loads(corrective._git_blob(corrective.CONSUMER_MAP_REL))
    paths = [row["path"] for row in source_map["consumers"]]
    assert len(paths) == 496
    assert all(validator.is_valid(path) for path in paths)
    for required in [".gitattributes", ".vscode/settings.json", "Physics Imps and Sigs.txt"]:
        assert required in paths
        assert validator.is_valid(required)
    for invalid in [
        "/absolute/report.json",
        "//server/share/report.json",
        "C:/drive/report.json",
        "../report.json",
        "a/../report.json",
        "a\\report.json",
        "a//report.json",
        "a\x00report.json",
    ]:
        assert not validator.is_valid(invalid), invalid


def test_prototype_path_profile_remains_strict_and_field_specific() -> None:
    schemas = _payload(corrective.SCHEMA_PATH)["schemas"]
    strict = schemas["validation_report"]["oneOf"][1]["properties"]["issues"][
        "items"
    ]["properties"]["artifact_path"]
    validator = Draft202012Validator(strict)
    assert validator.is_valid("validation/report.json")
    for invalid in [
        "/absolute/report.json",
        "//server/share/report.json",
        ".hidden/report.json",
        "path with spaces/report.json",
        "../report.json",
        "a\\report.json",
    ]:
        assert not validator.is_valid(invalid), invalid
    profiles = _payload(corrective.SCHEMA_PATH)["path_profiles"]
    assert set(profiles) == {
        "JSON_POINTER",
        "PROTOTYPE_ARTIFACT_RELPATH",
        "REPOSITORY_RELPATH",
        "RUN_ID",
        "SHARD_FILENAME",
    }


def test_validator_issue_interface_matches_report_and_accepts_both_control_namespaces() -> None:
    protocol = _payload(corrective.PROTOCOL_PATH)
    interface_issue = protocol["production_validator_interface"]["error_result"]
    schema_issue = _payload(corrective.SCHEMA_PATH)["schemas"]["validation_report"][
        "oneOf"
    ][1]["properties"]["issues"]["items"]
    assert interface_issue == schema_issue
    validator = Draft202012Validator(interface_issue)
    for control_id in ["REGISTRY-V1-NC-001", "REGISTRY-READINESS-V1-RC-008"]:
        issue = {
            "artifact_path": "validation/report.json",
            "control_id": control_id,
            "error_code": "V1-E-TEST",
            "json_pointer": "",
            "message": "probe",
        }
        assert validator.is_valid(issue)
        for bad_path in ["/absolute/report.json", "//server/share/report.json"]:
            bad = _copy(issue)
            bad["artifact_path"] = bad_path
            assert not validator.is_valid(bad)
    report_contract = protocol["production_validator_interface"]["report_contract"]
    assert "issues" in report_contract
    assert "errors" not in report_contract
    assert report_contract["issue_schema_shared_with_validation_report"] is True


def test_validation_report_schema_binds_exact_profile_closure_count_and_root() -> None:
    protocol = _payload(corrective.PROTOCOL_PATH)
    schema = _payload(corrective.SCHEMA_PATH)["schemas"]["validation_report"]
    profile = protocol["validator_profile_composition"]["named_entrypoints"][
        "CUTOVER_ELIGIBILITY"
    ]
    valid = {
        "candidate_root_sha256": "0" * 64,
        "effective_control_count": 52,
        "executed_profile_closure": profile["ordered_closure"],
        "issues": [],
        "passed": True,
        "profile": "CUTOVER_ELIGIBILITY",
        "profile_control_root_sha256": profile["effective_control_root_sha256"],
        "schema_id": "LOOP_CONTROL_VALIDATION_REPORT_READINESS_v2",
        "status": "PASSED",
        "trust_anchor_sha256": "1" * 64,
    }
    validator = Draft202012Validator(schema)
    assert validator.is_valid(valid)
    direct_only = _copy(valid)
    direct_only["executed_profile_closure"] = ["CUTOVER_ELIGIBILITY"]
    assert not validator.is_valid(direct_only)
    wrong_root = _copy(valid)
    wrong_root["profile_control_root_sha256"] = "f" * 64
    assert not validator.is_valid(wrong_root)


def test_all_eight_regressions_are_atomic_executable_singleton_contracts() -> None:
    harness = _payload(corrective.PROTOCOL_PATH)["typed_control_harness"]
    rows = harness["readiness_regressions"]
    assert harness["readiness_regression_control_count"] == len(rows) == 8
    assert harness["readiness_regression_atomic_case_count"] == 8
    required = {
        "artifact_kind",
        "baseline_candidate_recreated_before_mutation",
        "control_id",
        "control_sequence",
        "error_phase",
        "error_precedence_rank",
        "execution_status",
        "expected_decision",
        "expected_exact_error_set",
        "fixture_isolation",
        "mutation_matrix",
        "mutation_precondition",
        "mutator_entrypoint",
        "positive_fixture_contract_sha256",
        "positive_fixture_id",
        "rebind_candidate_internal_hashes",
        "subsequent_controls_receive_unmodified_baseline",
        "validator_entrypoint",
        "validator_profile",
    }
    assert all(required.issubset(row) for row in rows)
    assert all(len(row["mutation_matrix"]) == 1 for row in rows)
    assert all(len(row["expected_exact_error_set"]) == 1 for row in rows)
    assert [row["control_sequence"] for row in rows] == list(range(1, 9))
    assert [row["error_precedence_rank"] for row in rows] == [5, 2, 3, 4, 1, 1, 6, 6]
    assert len({row["positive_fixture_contract_sha256"] for row in rows}) == 6
    aggregation = harness["readiness_error_aggregation"]
    assert aggregation["multiple_errors_for_one_atomic_case_allowed"] is False
    assert aggregation[
        "control_passes_only_if_every_matrix_case_returns_exact_singleton_error"
    ] is True


def test_atomic_regression_vectors_match_the_eight_reviewed_false_accepts() -> None:
    rows = {
        row["control_id"]: row
        for row in _payload(corrective.PROTOCOL_PATH)["typed_control_harness"][
            "readiness_regressions"
        ]
    }
    assert rows["REGISTRY-READINESS-V1-RC-002"]["mutation_matrix"][0]["after"] == (
        "Zh=="
    )
    assert rows["REGISTRY-READINESS-V1-RC-003"]["mutation_matrix"][0] == {
        "after": 5,
        "before": 4,
        "case_id": "REGISTRY-READINESS-V1-RC-003-CASE-001",
        "json_pointer": "/payload_size_bytes",
        "rebind_fields": [],
    }
    assert rows["REGISTRY-READINESS-V1-RC-005"]["mutation_matrix"][0]["after"] == (
        "/absolute/report.json"
    )
    assert rows["REGISTRY-READINESS-V1-RC-006"]["mutation_matrix"][0]["after"] == (
        "//server/share/report.json"
    )
    assert rows["REGISTRY-READINESS-V1-RC-008"]["mutation_matrix"][0][
        "json_pointer"
    ] == "/base_candidate_sha256_after"


def test_record_identity_and_all_three_root_byte_algorithms_are_complete() -> None:
    payload = _payload(corrective.PROTOCOL_PATH)["history_payload_validation_algorithm"]
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
    assert "COLON_PAYLOAD_SHA256_COLON_POINTER" in payload[
        "identity_payload_pointer_root_algorithm"
    ]
    assert payload["original_pointer_root_algorithm"].endswith(
        "JOIN_UTF8_LF_NO_TERMINAL_LF_SHA256"
    )


def test_shadow_manifest_explicitly_attests_no_migration_or_cutover() -> None:
    shadow = _payload(corrective.SCHEMA_PATH)["schemas"][
        "runtime_shadow_trace_manifest"
    ]
    props = shadow["properties"]
    assert props["consumer_migration_performed"] == {
        "const": False,
        "type": "boolean",
    }
    assert props["cutover_performed"] == {"const": False, "type": "boolean"}
    assert {"consumer_migration_performed", "cutover_performed"}.issubset(
        shadow["required"]
    )
    invariants = _payload(corrective.PROTOCOL_PATH)["success_report_invariants"][
        "shadow_manifest"
    ]
    assert "CONSUMER_MIGRATION_PERFORMED_FALSE" in invariants
    assert "CUTOVER_PERFORMED_FALSE" in invariants
    assert "EVERY_EVENT_RUN_ID_EQUALS_MANIFEST_RUN_ID" in invariants


def test_v2_preserves_all_nonauthorization_and_production_absence() -> None:
    packet = _payload(corrective.PACKET_PATH)
    assert packet["authorization"]["scientific_target"] == corrective.SCIENTIFIC_TARGET
    assert packet["authorization"]["maintenance_target"] == corrective.MAINTENANCE_TARGET
    assert packet["authorization"]["packet_target_is_current_maintenance_authority"] is False
    assert packet["authorization"]["prototype_execution_target_selected"] is False
    assert packet["authorization"]["registry_migration_execution_authorized"] is False
    assert packet["authorization"]["registry_cutover_authorized"] is False
    assert all(value is False for value in packet["boundary"].values())
    assert all(value is False for key, value in packet["selection_posture"].items() if key.endswith("selectable"))
    for path in corrective.FORBIDDEN_PATHS:
        assert not (corrective.REPO_ROOT / path).exists()


def test_v2_lean_certificate_binds_artifacts_rejection_and_nonauthorization() -> None:
    lean = (
        corrective.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingExecutionReadinessPacketV2.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_PACKET_SHA256 in lean
    assert EXPECTED_PROTOCOL_SHA256 in lean
    assert EXPECTED_SCHEMA_SHA256 in lean
    assert corrective.EXPECTED_SHA256[corrective.V1_REVIEW_REL] in lean
    assert corrective.SCIENTIFIC_TARGET in lean
    assert corrective.MAINTENANCE_TARGET in lean
    assert "correctiveV2IndependentReviewRequired : Bool := true" in lean
    assert "prototypeExecutionSelected : Bool := false" in lean
    assert "migrationExecutionAuthorized : Bool := false" in lean
    assert "registryCutoverAuthorized : Bool := false" in lean
