from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from typing import Any

from jsonschema import Draft202012Validator
from jsonschema.validators import validator_for

from formal.python.tools import (
    loop_control_registry_sharding_execution_readiness_packet_v1 as corrective,
)


EXPECTED_PACKET_SHA256 = "ba7275826efe754c9cdc611df32fdc4ea257017d826757de0e63206299db0261"
EXPECTED_PROTOCOL_SHA256 = "4cb61f06e95db05593a1d9918408ceaa0cbfcc503d3720c50a8c5816781c5014"
EXPECTED_SCHEMA_SHA256 = "11b6f870fd57dbc2f325d3aaa9dc5d99e4c1da303e3cee3db182f6e29f020d55"


def _payload(path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


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


def test_corrective_v1_artifacts_are_deterministic() -> None:
    expected = {
        corrective.PACKET_PATH: EXPECTED_PACKET_SHA256,
        corrective.PROTOCOL_PATH: EXPECTED_PROTOCOL_SHA256,
        corrective.SCHEMA_PATH: EXPECTED_SCHEMA_SHA256,
    }
    artifacts = corrective.build_all()
    assert set(artifacts) == set(expected)
    for path, sha256 in expected.items():
        assert path.read_bytes() == artifacts[path]
        assert hashlib.sha256(artifacts[path]).hexdigest() == sha256


def test_corrective_v1_cli_check_is_read_only() -> None:
    before = {path: path.read_bytes() for path in corrective.build_all()}
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.loop_control_registry_sharding_execution_readiness_packet_v1",
            "--check",
        ],
        cwd=corrective.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert {path: path.read_bytes() for path in before} == before


def test_v0_rejection_and_all_v0_artifact_bytes_remain_immutable() -> None:
    for path, expected in corrective.EXPECTED_SHA256.items():
        raw = corrective._git_blob(path)
        assert hashlib.sha256(raw).hexdigest() == expected
    packet = _payload(corrective.PACKET_PATH)
    custody = packet["rejected_v0_custody"]
    assert custody["v0_execution_readiness_accepted"] is False
    assert custody["v0_preserved_as_historical_preparation_evidence"] is True
    assert custody["review_sha256"] == corrective.EXPECTED_SHA256[corrective.V0_REVIEW_REL]


def test_all_ten_v1_schemas_pass_metaschema_and_recursive_closure() -> None:
    bundle = _payload(corrective.SCHEMA_PATH)
    assert bundle["schema_count"] == len(bundle["schemas"]) == 10
    for name, schema in bundle["schemas"].items():
        validator_for(schema).check_schema(schema)
        _assert_closed(schema)
        assert "/readiness-v1/" in schema["$id"], name
    assert bundle["semantic_validation_boundary"] == {
        "json_schema_only_success_authorized": False,
        "success_requires": [
            "STRUCTURAL_JSON_SCHEMA",
            "STRICT_PARSER_PROFILE",
            "NAMED_SEMANTIC_VALIDATION_PROFILE",
            "EXTERNAL_TRUST_ANCHOR_COMPARISON",
        ],
    }


def test_repository_path_schema_rejects_v0_absolute_unc_and_traversal_false_accepts() -> None:
    schema = _payload(corrective.SCHEMA_PATH)["schemas"]["current_projection"]
    path_schema = schema["properties"]["source_legacy_identity"]["properties"]["path"]
    validator = Draft202012Validator(path_schema)
    accepted = [
        "projection/LOOP_CONTROL_CURRENT_v1.prototype.json",
        "history/shards/LOOP_CONTROL_HISTORY_0001.jsonl",
    ]
    rejected = [
        "/tmp/registry.json",
        "//server/share/registry.json",
        "C:/registry.json",
        "../registry.json",
        "history/../registry.json",
        "history\\registry.json",
        "history//registry.json",
        ".",
        "history/.",
        "history/*.jsonl",
    ]
    assert all(validator.is_valid(path) for path in accepted)
    assert all(not validator.is_valid(path) for path in rejected)
    contract = _payload(corrective.PROTOCOL_PATH)["repository_path_validation_algorithm"]
    assert contract["lexical_prefix_check_sufficient"] is False
    assert "REJECT_SYMLINK_JUNCTION_OR_REPARSE_POINT_IN_EVERY_EXISTING_ANCESTOR" in (
        contract["mandatory_ordered_steps"]
    )
    assert "REQUIRE_TARGET_STRICTLY_WITHIN_EXACT_RUN_ROOT_BY_COMMONPATH" in (
        contract["mandatory_ordered_steps"]
    )


def test_history_base64_schema_rejects_bad_alphabet_whitespace_and_padding() -> None:
    record = _payload(corrective.SCHEMA_PATH)["schemas"]["history_shard_record"]
    payload_schema = record["properties"]["payload_canonical_json_utf8_base64"]
    validator = Draft202012Validator(payload_schema)
    assert validator.is_valid("bnVsbA==")
    for invalid in ["!!!!", "bnVsbA", "bnVsbA==\n", "bnVsbA__", "A===", "===="]:
        assert not validator.is_valid(invalid), invalid
    assert payload_schema["maxLength"] == corrective.MAX_PAYLOAD_BASE64_BYTES
    assert record["properties"]["payload_size_bytes"]["maximum"] == (
        corrective.MAX_PAYLOAD_BYTES
    )


def test_history_payload_semantic_algorithm_freezes_every_cross_field_check() -> None:
    algorithm = _payload(corrective.PROTOCOL_PATH)["history_payload_validation_algorithm"]
    assert algorithm["json_schema_only_success_authorized"] is False
    assert algorithm["maximum_decoded_bytes"] == 2_124_270
    assert algorithm["maximum_encoded_bytes"] == 2_832_360
    assert algorithm["mandatory_ordered_steps"] == [
        "STRICT_RFC4648_BASE64_DECODE_VALIDATE_TRUE_AND_EXACT_REENCODE",
        "DECODED_LENGTH_EQUALS_PAYLOAD_SIZE_BYTES",
        "DECODED_SHA256_EQUALS_PAYLOAD_SHA256",
        "STRICT_UTF8_DUPLICATE_KEY_AND_NONFINITE_JSON_PARSE",
        "COMPACT_CANONICAL_RESERIALIZATION_EQUALS_DECODED_BYTES",
        "PARSED_TOP_LEVEL_TYPE_EQUALS_PAYLOAD_KIND_BOOL_BEFORE_NUMBER",
        "LOGICAL_KEY_POINTER_SOURCE_AND_OCCURRENCE_MATCH_SOURCE_RECORD",
        "RECOMPUTE_LOOP_CONTROL_RECORD_ID_V1_PREIMAGE",
        "RECOMPUTED_LCR1_SHA256_EQUALS_RECORD_ID",
        "FULL_RECORD_ROOTS_EQUAL_EXTERNALLY_REVIEWED_ROOTS",
    ]
    expected_fields = [
        "domain",
        "record_class",
        "source_path",
        "source_git_blob",
        "logical_key",
        "original_json_pointer",
        "payload_sha256",
        "identical_occurrence_ordinal",
    ]
    assert algorithm["record_id_preimage_fields"] == expected_fields
    index = _payload(corrective.SCHEMA_PATH)["schemas"]["history_index"]
    frozen = index["properties"]["record_identity_contract"]["properties"][
        "preimage_fields"
    ]["const"]
    assert frozen == expected_fields


def test_profile_composition_has_exact_unambiguous_ordered_closures_and_roots() -> None:
    composition = _payload(corrective.PROTOCOL_PATH)["validator_profile_composition"]
    assert composition["generic_profile_parameter_allowed"] is False
    assert composition["candidate_selectable_profile_allowed"] is False
    assert composition["effective_profile_invocation_count"] == 199
    expected = {
        "PROTOTYPE_INTEGRITY": (["PROTOTYPE_INTEGRITY"], 47),
        "WRITE_SAFETY": (["PROTOTYPE_INTEGRITY", "WRITE_SAFETY"], 49),
        "SHADOW_PARITY": (
            ["PROTOTYPE_INTEGRITY", "WRITE_SAFETY", "SHADOW_PARITY"],
            51,
        ),
        "CUTOVER_ELIGIBILITY": (
            [
                "PROTOTYPE_INTEGRITY",
                "WRITE_SAFETY",
                "SHADOW_PARITY",
                "CUTOVER_ELIGIBILITY",
            ],
            52,
        ),
    }
    for name, (closure, count) in expected.items():
        row = composition["named_entrypoints"][name]
        assert row["ordered_closure"] == closure
        assert row["effective_control_count"] == count
        assert row["effective_control_root_sha256"] == hashlib.sha256(
            "\n".join(row["effective_control_ids"]).encode("utf-8")
        ).hexdigest()
    cutover = composition["named_entrypoints"]["CUTOVER_ELIGIBILITY"]
    assert cutover["live_legacy_reader_requirement"] == "FORBIDDEN_AT_CUTOVER"
    assert cutover["shadow_stage_semantics"] == (
        "VERIFY_PREVIOUSLY_ACCEPTED_IMMUTABLE_SHADOW_MANIFEST_NO_LIVE_DUAL_READ"
    )
    assert "extends" not in json.dumps(composition)


def test_original_52_controls_are_preserved_and_eight_regressions_are_separate() -> None:
    protocol = _payload(corrective.PROTOCOL_PATH)
    harness = protocol["typed_control_harness"]
    baseline = json.loads(corrective._git_blob(corrective.V0_PROTOCOL_REL))[
        "typed_control_harness"
    ]
    assert harness["controls"] == baseline["controls"]
    assert harness["migration_control_count"] == len(harness["controls"]) == 52
    regressions = harness["readiness_regressions"]
    assert harness["readiness_regression_control_count"] == len(regressions) == 8
    assert harness["distinct_control_count"] == 60
    assert len({row["control_id"] for row in regressions}) == 8
    assert len({row["expected_exact_error_set"][0] for row in regressions}) == 8
    assert all(row["permanent"] for row in regressions)
    assert all(row["v0_false_acceptance_regression"] for row in regressions)
    assert all(
        row["execution_status"] == "NOT_EXECUTED_CORRECTIVE_PREPARATION_ONLY"
        for row in regressions
    )


def _valid_validation_report() -> dict[str, Any]:
    return {
        "candidate_root_sha256": "0" * 64,
        "executed_profile_closure": ["PROTOTYPE_INTEGRITY"],
        "issues": [],
        "passed": True,
        "profile": "PROTOTYPE_INTEGRITY",
        "profile_control_root_sha256": "1" * 64,
        "schema_id": "LOOP_CONTROL_VALIDATION_REPORT_READINESS_v1",
        "status": "PASSED",
        "trust_anchor_sha256": "2" * 64,
    }


def test_validation_report_schema_rejects_contradictory_pass_and_fail_claims() -> None:
    schema = _payload(corrective.SCHEMA_PATH)["schemas"]["validation_report"]
    validator = Draft202012Validator(schema)
    passed = _valid_validation_report()
    assert validator.is_valid(passed)
    issue = {
        "artifact_path": "validation/report.json",
        "control_id": None,
        "error_code": "V1-E-TEST",
        "json_pointer": "",
        "message": "probe",
    }
    contradictory = deepcopy_json(passed)
    contradictory["issues"] = [issue]
    assert not validator.is_valid(contradictory)
    failed_without_issue = deepcopy_json(passed)
    failed_without_issue.update({"issues": [], "passed": False, "status": "FAILED"})
    assert not validator.is_valid(failed_without_issue)


def deepcopy_json(value: Any) -> Any:
    return json.loads(json.dumps(value))


def _profile_report(direct: int, effective: int, marker: str) -> dict[str, Any]:
    return {
        "baseline_after_passed": True,
        "baseline_before_passed": True,
        "baseline_candidate_sha256": marker * 64,
        "direct_control_count": direct,
        "direct_controls_passed": direct,
        "effective_control_count": effective,
        "effective_control_root_sha256": "f" * 64,
        "effective_controls_passed": effective,
    }


def test_harness_and_shadow_success_schemas_freeze_structural_truth_conditions() -> None:
    schemas = _payload(corrective.SCHEMA_PATH)["schemas"]
    harness = {
        "base_candidate_sha256_after": "a" * 64,
        "base_candidate_sha256_before": "a" * 64,
        "distinct_control_count": 60,
        "effective_profile_invocation_count": 199,
        "migration_control_count": 52,
        "migration_controls_passed": 52,
        "profile_reports": {
            "CUTOVER_ELIGIBILITY": _profile_report(1, 52, "a"),
            "PROTOTYPE_INTEGRITY": _profile_report(47, 47, "a"),
            "SHADOW_PARITY": _profile_report(2, 51, "a"),
            "WRITE_SAFETY": _profile_report(2, 49, "a"),
        },
        "readiness_regression_control_count": 8,
        "readiness_regressions_passed": 8,
        "schema_id": "LOOP_CONTROL_CONTROL_HARNESS_REPORT_READINESS_v1",
        "status": "ALL_CONTROLS_PASSED",
    }
    validator = Draft202012Validator(schemas["control_harness_report"])
    assert validator.is_valid(harness)
    bad = deepcopy_json(harness)
    bad["profile_reports"]["WRITE_SAFETY"]["effective_controls_passed"] = 48
    assert not validator.is_valid(bad)
    shadow_props = schemas["runtime_shadow_trace_manifest"]["properties"]
    assert shadow_props["migration_batch_coverage_complete"]["const"] is True
    assert shadow_props["operation_class_coverage_complete"]["const"] is True
    assert shadow_props["unobserved_required_consumer_count"]["const"] == 0
    invariants = _payload(corrective.PROTOCOL_PATH)["success_report_invariants"]
    assert "BASE_CANDIDATE_SHA256_BEFORE_EQUALS_AFTER" in invariants[
        "control_harness_report"
    ]
    assert "OBSERVED_PLUS_UNOBSERVED_EQUALS_REQUIRED_CONSUMER_COUNT" in invariants[
        "shadow_manifest"
    ]


def test_prototype_paths_are_relative_allowlisted_and_have_no_templates_or_globs() -> None:
    paths = _payload(corrective.PROTOCOL_PATH)["prototype_paths"]
    assert paths["prototype_base_repo_relative"] == (
        "formal/scratch/loop_control_registry_v1_prototype"
    )
    assert paths["run_id_pattern"] == "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$"
    for path in paths["artifact_paths_relative_to_run_root"].values():
        assert re.fullmatch(corrective.PATH_PATTERN, path)
        assert "<run_id>" not in path
        assert "*" not in path
    assert paths["history_shard_filename_pattern"] == (
        "^LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$"
    )


def test_corrective_v1_preserves_authority_and_historical_path_absence() -> None:
    packet = _payload(corrective.PACKET_PATH)
    assert packet["authorization"]["scientific_target"] == corrective.SCIENTIFIC_TARGET
    assert packet["authorization"]["maintenance_target"] == corrective.MAINTENANCE_TARGET
    assert packet["authorization"]["packet_target_is_current_maintenance_authority"] is False
    assert packet["authorization"]["prototype_execution_target_selected"] is False
    assert packet["authorization"]["registry_migration_execution_authorized"] is False
    assert packet["authorization"]["registry_cutover_authorized"] is False
    assert all(value is False for value in packet["boundary"].values())
    assert packet["selection_posture"] == {
        "corrective_v1_acceptance_would_prove_only": (
            "CORRECTED_PREPARATION_CONTRACT_SURVIVED_INDEPENDENT_ADVERSARIAL_REVIEW"
        ),
        "cutover_selectable": False,
        "migration_execution_selectable": False,
        "prototype_execution_selectable": False,
    }
    for path in corrective.FORBIDDEN_PATHS:
        assert not corrective._path_exists_at_source_commit(path)


def test_lean_certificate_binds_corrective_artifacts_and_all_nonauthorizations() -> None:
    lean = (
        corrective.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingExecutionReadinessPacketV1.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_PACKET_SHA256 in lean
    assert EXPECTED_PROTOCOL_SHA256 in lean
    assert EXPECTED_SCHEMA_SHA256 in lean
    assert corrective.EXPECTED_SHA256[corrective.V0_REVIEW_REL] in lean
    assert corrective.SCIENTIFIC_TARGET in lean
    assert corrective.MAINTENANCE_TARGET in lean
    assert "prototypeExecutionSelected : Bool := false" in lean
    assert "migrationExecutionAuthorized : Bool := false" in lean
    assert "registryCutoverAuthorized : Bool := false" in lean
    assert "unitLedgerExecuted : Bool := false" in lean
