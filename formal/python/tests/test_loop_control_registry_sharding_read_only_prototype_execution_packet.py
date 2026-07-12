from __future__ import annotations

import base64
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Any, Iterator

from jsonschema import Draft202012Validator, FormatChecker
from jsonschema.validators import validator_for

from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution_packet as preparation,
)


SHA0 = "0" * 64
SHA1 = "1" * 64
COMMIT1 = "1" * 40
RUN_ID = "prototype_stage_a"

EXPECTED_RUNTIME_SCHEMAS = {
    "artifact_source_manifest",
    "execution_preflight",
    "reviewed_trust_anchors",
    "run_rollback_inventory",
    "runtime_run_manifest",
    "stage_a_acceptance_binding",
    "stage_a_precutover_report",
    "stage_b_full_harness_result",
    "typed_result_envelope",
    "writer_probe",
}

EXPECTED_HISTORICAL_GATES = [
    ("v0_preparation", "bf8c12918675d77c27c0eadde009134fc572c281"),
    (
        "v0_corrected_pre_review_boundary",
        "a0d44da40922d6547f02241174fa640edb3f9fa8",
    ),
    ("v0_review", "be985ab12d1947b188d773aaf5d9f64de097770e"),
    ("v1_preparation", "e2af09bbb4355604eee4566707afd3407ed6c4b9"),
    ("v1_review", "5f6672b13f1bff7653cb7caa3fc5b4e80276fc2a"),
    ("v2_preparation", "20a57192305cc794397fdcef06f54cab30c37205"),
    ("v2_review", "ee287de3db44bd4fe5a1c9c9952c07be9d2e9248"),
    ("v3_preparation", "f9051af27988dd745bf39d28ae4d610973d5a029"),
    ("v3_review", preparation.SOURCE_COMMIT),
]


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _packet() -> dict[str, Any]:
    return _load(preparation.PACKET_PATH)


def _contract() -> dict[str, Any]:
    return _load(preparation.CONTRACT_PATH)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=preparation.REPO_ROOT,
        capture_output=True,
        text=True,
        check=check,
    )


def _walk(value: Any, pointer: str = "") -> Iterator[tuple[str, Any]]:
    yield pointer, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from _walk(child, f"{pointer}/{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from _walk(child, f"{pointer}/{index}")


def _validator(schema: dict[str, Any]) -> Draft202012Validator:
    return Draft202012Validator(schema, format_checker=FormatChecker())


def _identity(path: str = "validation/evidence.json") -> dict[str, Any]:
    return {"path": path, "sha256": SHA0, "size_bytes": 1}


def _stage_a_rows(contract: dict[str, Any]) -> list[dict[str, Any]]:
    harness = contract["control_harness_contract"]
    rows = {
        row["control_id"]: row
        for row in harness["primary_controls"] + harness["readiness_controls"]
    }
    order = contract["lifecycle"][
        "stage_a_precutover_execution_after_separate_authorization"
    ]["control_result_order"]
    return [rows[control_id] for control_id in order]


def _stage_a_control_results(contract: dict[str, Any]) -> list[dict[str, Any]]:
    error_map = contract["control_harness_contract"]["control_error_map"]
    return [
        {
            "control_id": row["control_id"],
            "validator_profile": row["validator_profile"],
            "expected_decision": "REJECT",
            "observed_decision": "REJECT",
            "expected_error_codes": [error_map[row["control_id"]]],
            "observed_error_codes": [error_map[row["control_id"]]],
            "baseline_candidate_sha256_before": SHA0,
            "baseline_candidate_sha256_after": SHA0,
            "positive_baseline_passed_before_mutation": True,
            "baseline_recreated_for_control": True,
            "subsequent_controls_received_unmodified_baseline": True,
            "passed": True,
        }
        for row in _stage_a_rows(contract)
    ]


def _positive_fixtures(contract: dict[str, Any]) -> dict[str, dict[str, Any]]:
    source_registry = {
        "source_commit": "f9168ab5f566fb2019b9e76e68ff3e60e5c0dc52",
        "path": preparation.REGISTRY,
        "git_blob": preparation.EXPECTED[preparation.REGISTRY][1],
        "sha256": preparation.EXPECTED[preparation.REGISTRY][0],
        "size_bytes": preparation.EXPECTED[preparation.REGISTRY][2],
    }
    authorization = {
        "packet_path": preparation.PACKET_PATH.relative_to(
            preparation.REPO_ROOT
        ).as_posix(),
        "packet_sha256": SHA0,
        "reviewed_packet_commit": COMMIT1,
        "independent_review_path": preparation.PACKET_REVIEW_PATH,
        "independent_review_sha256": SHA1,
        "authorization_review_commit": COMMIT1,
        "bounded_stage_a_authorized": True,
        "stage_b_authorized": False,
        "anchor_source": "GIT_COMMIT_VERIFIED_INDEPENDENT_REVIEW",
    }
    anchors = {
        "schema_id": "LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1",
        "v3_acceptance_commit": preparation.SOURCE_COMMIT,
        "accepted_v3_review": {
            "path": preparation.V3_REVIEW,
            "sha256": preparation.EXPECTED[preparation.V3_REVIEW][0],
            "reviewed_preparation_commit": (
                "f9051af27988dd745bf39d28ae4d610973d5a029"
            ),
        },
        "v3_contract": {
            "packet_sha256": preparation.EXPECTED[preparation.V3_PACKET][0],
            "protocol_sha256": preparation.EXPECTED[preparation.V3_PROTOCOL][0],
            "schema_bundle_sha256": preparation.EXPECTED[preparation.V3_SCHEMAS][0],
        },
        "external_v1": {
            "source_commit": "6aba59d8d399b331db010f1f5f857075b9100b7f",
            "guardrail_sha256": preparation.EXPECTED[preparation.V1_GUARDRAIL][0],
            "review_sha256": preparation.EXPECTED[preparation.V1_REVIEW][0],
        },
        "source_registry": source_registry,
        "authority_commitment_sha256": (
            "fd4348411236648d6216900eced59524b87c561bfa0d36186cf4c4d19a2e6b34"
        ),
        "requirements_lock_sha256": preparation.EXPECTED[preparation.REQUIREMENTS][0],
        "prototype_execution_authorization": authorization,
        "candidate_supplied_values_authoritative": False,
    }
    artifact_source = {
        "schema_id": "LOOP_CONTROL_ARTIFACT_SOURCE_MANIFEST_v1",
        "run_id": RUN_ID,
        "source_commit": preparation.SOURCE_COMMIT,
        "implementation_commit": COMMIT1,
        "run_root_repo_relative": (
            f"formal/scratch/loop_control_registry_v1_prototype/{RUN_ID}"
        ),
        "candidate_tree_sha256": SHA0,
        "inventory_sha256": SHA1,
        "inventory_algorithm_id": "LOOP_CONTROL_RUN_ARTIFACT_INVENTORY_ROOT_v1",
        "candidate_tree_algorithm_id": (
            "LOOP_CONTROL_CANDIDATE_PAYLOAD_TREE_ROOT_v1"
        ),
        "candidate_payload_artifact_count": 1,
        "evidence_artifact_count": 0,
        "artifacts": [
            {
                "artifact_kind": "CURRENT_PROJECTION",
                "candidate_payload": True,
                "path": "projection/LOOP_CONTROL_CURRENT_v1.prototype.json",
                "sha256": SHA0,
                "size_bytes": 1,
            }
        ],
        "immutable": True,
    }
    writer_probe = {
        "schema_id": "LOOP_CONTROL_WRITER_PROBE_v1",
        "run_id": RUN_ID,
        "attempted_writes": [],
        "writes_outside_run_root": 0,
        "history_mutation_performed": False,
        "new_api_write_performed": False,
        "source_registry_sha256_before": preparation.EXPECTED[preparation.REGISTRY][0],
        "source_registry_sha256_after": preparation.EXPECTED[preparation.REGISTRY][0],
    }
    rollback = {
        "schema_id": "LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v1",
        "run_id": RUN_ID,
        "run_root_repo_relative": (
            f"formal/scratch/loop_control_registry_v1_prototype/{RUN_ID}"
        ),
        "pre_run_inventory_sha256": SHA0,
        "created_paths": [],
        "created_paths_root_sha256": SHA1,
        "outside_run_root_created_path_count": 0,
        "rollback_eligible": True,
    }
    null_bytes = b"null"
    typed_result = {
        "result_kind": "VALUE",
        "type_tag": "JSON",
        "canonical_json_utf8_base64": base64.b64encode(null_bytes).decode("ascii"),
        "payload_sha256": _sha256(null_bytes),
    }
    profile_roots = {
        name: schema["const"]
        for name, schema in contract["runtime_schemas"][
            "stage_a_precutover_report"
        ]["properties"]["stage_a_profile_control_roots"]["properties"].items()
    }
    stage_a = {
        "schema_id": "LOOP_CONTROL_STAGE_A_PRECUTOVER_REPORT_v1",
        "run_id": RUN_ID,
        "candidate_tree_sha256": SHA0,
        "primary_controls_passed": 51,
        "readiness_controls_passed": 7,
        "distinct_controls_passed": 58,
        "runtime_contract_controls_passed": len(preparation.RUNTIME_NEGATIVE_CONTROLS),
        "total_controls_passed": 58 + len(preparation.RUNTIME_NEGATIVE_CONTROLS),
        "cutover_controls_executed": False,
        "final_harness_report_emitted": False,
        "control_results": _stage_a_control_results(contract),
        "control_results_root_sha256": SHA1,
        "runtime_contract_control_results": [
            {
                "control_id": control_id,
                "mutation": mutation,
                "expected_error": error,
                "observed_error": error,
                "fresh_baseline": True,
                "subsequent_controls_unmodified": True,
                "passed": True,
            }
            for control_id, mutation, error in preparation.RUNTIME_NEGATIVE_CONTROLS
        ],
        "runtime_contract_results_root_sha256": SHA0,
        "stage_a_profile_control_roots": profile_roots,
        "baseline_isolation_verified": True,
        "shadow_manifest": _identity("traces/shadow-manifest.json"),
        "custody_manifest": _identity("custody/custody-manifest.json"),
        "reconstruction_result": _identity("compat/reconstruction-result.json"),
        "status": "PRE_CUTOVER_EVIDENCE_COMPLETE_REVIEW_REQUIRED",
    }
    stage_a_binding = {
        "schema_id": "LOOP_CONTROL_STAGE_A_ACCEPTANCE_BINDING_v1",
        "review_commit": COMMIT1,
        "review_path": preparation.STAGE_A_REVIEW_PATH,
        "review_sha256": SHA0,
        "review_schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_STAGE_A_"
            "INDEPENDENT_REVIEW_20260711_v0"
        ),
        "review_target": preparation.STAGE_A_REVIEW_TARGET,
        "implementation_commit": COMMIT1,
        "candidate_tree_sha256": SHA0,
        "stage_a_report_path": "validation/stage-a-report.json",
        "stage_a_report_sha256": SHA1,
        "shadow_manifest_path": "traces/shadow-manifest.json",
        "shadow_manifest_sha256": SHA1,
        "shadow_run_id": RUN_ID,
        "accepted": True,
        "stage_b_full_harness_authorized": False,
        "stage_b_successor_packet_required": True,
        "migration_execution_authorized": False,
        "cutover_authorized": False,
    }
    stage_b = {
        "schema_id": "LOOP_CONTROL_STAGE_B_FULL_HARNESS_RESULT_v1",
        "run_id": RUN_ID,
        "candidate_tree_sha256": SHA0,
        "accepted_stage_a": stage_a_binding,
        "primary_controls_passed": 52,
        "readiness_controls_passed": 8,
        "distinct_controls_passed": 60,
        "runtime_contract_controls_passed": len(preparation.RUNTIME_NEGATIVE_CONTROLS),
        "total_controls_passed": 60 + len(preparation.RUNTIME_NEGATIVE_CONTROLS),
        "effective_profile_invocations_passed": 199,
        "control_harness_report": _identity("validation/control-harness.json"),
        "migration_execution_authorized": False,
        "cutover_authorized": False,
        "status": "FULL_READ_ONLY_HARNESS_COMPLETE_REVIEW_REQUIRED",
    }
    runtime_manifest = {
        "schema_id": "LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v1",
        "run_id": RUN_ID,
        "stage": "STAGE_A",
        "reviewed_trust_anchors_sha256": SHA0,
        "artifact_source_manifest": _identity("manifests/artifact-source.json"),
        "writer_probe": _identity("validation/writer-probe.json"),
        "rollback_inventory": _identity("manifests/rollback.json"),
        "started_at_utc": "2026-07-11T00:00:00Z",
        "finished_at_utc": "2026-07-11T00:00:01Z",
        "timed_out": False,
        "pre_run_detached_checkout_clean": True,
        "post_run_only_allowlisted_run_root_changes": True,
        "post_run_protected_files_unchanged": True,
    }
    preflight = {
        "schema_id": "LOOP_CONTROL_READ_ONLY_PROTOTYPE_EXECUTION_PREFLIGHT_v1",
        "packet_review_path": preparation.PACKET_REVIEW_PATH,
        "packet_review_sha256": SHA0,
        "authorization_review_commit": COMMIT1,
        "authorization_review_is_ancestor_of_implementation": True,
        "implementation_commit": COMMIT1,
        "implementation_tree_sha256": SHA1,
        "head_commit": COMMIT1,
        "main_commit": COMMIT1,
        "origin_main_commit": COMMIT1,
        "main_equals_origin_main": True,
        "head_main_origin_equal_implementation_commit": True,
        "worktree_clean": True,
        "v3_acceptance_commit": preparation.SOURCE_COMMIT,
        "source_registry_sha256": preparation.EXPECTED[preparation.REGISTRY][0],
        "historical_record_count": 4691,
        "baseline_classified_consumer_path_count": 496,
        "baseline_consumer_map_sha256": preparation.EXPECTED[preparation.CONSUMER_MAP][0],
        "current_consumer_path_count": 496,
        "consumer_inventory_delta_root_sha256": SHA0,
        "consumer_inventory_rows": [
            {
                "path": f"formal/python/tests/consumer_{index:03d}.py",
                "delta_class": "UNCHANGED",
                "baseline_consumer_id": f"lcc1:{_sha256(f'baseline-{index}'.encode())}",
                "current_consumer_id": f"lcc1:{_sha256(f'current-{index}'.encode())}",
                "baseline_source_sha256": SHA0,
                "current_source_sha256": SHA0,
                "consumer_role": "TEST_ONLY_CONSUMER",
                "access_operation": "STATIC_READER_CANDIDATE",
                "disposition": "PROVED_NONRUNTIME",
                "disposition_reason": "positive schema fixture",
            }
            for index in range(496)
        ],
        "all_baseline_and_current_consumer_rows_dispositioned": True,
        "protected_bindings_reverified": True,
    }
    return {
        "reviewed_trust_anchors": anchors,
        "artifact_source_manifest": artifact_source,
        "writer_probe": writer_probe,
        "run_rollback_inventory": rollback,
        "typed_result_envelope": typed_result,
        "stage_a_precutover_report": stage_a,
        "stage_a_acceptance_binding": stage_a_binding,
        "stage_b_full_harness_result": stage_b,
        "runtime_run_manifest": runtime_manifest,
        "execution_preflight": preflight,
    }


def test_preparation_artifacts_are_deterministic_and_cli_check_is_read_only() -> None:
    built = preparation.build_all()
    assert set(built) == {preparation.PACKET_PATH, preparation.CONTRACT_PATH}
    before = {path: path.read_bytes() for path in built}
    assert built == before
    assert preparation.build_all() == built
    for raw in built.values():
        assert raw.startswith(b"\xef\xbb\xbf") is False
        assert b"\r\n" not in raw
        assert raw.endswith(b"\n") and not raw.endswith(b"\n\n")

    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.loop_control_registry_sharding_read_only_prototype_execution_packet",
            "--check",
        ],
        cwd=preparation.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr
    assert {path: path.read_bytes() for path in built} == before


def test_strict_json_rejects_duplicate_keys_and_nonfinite_values() -> None:
    for raw in (b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}'):
        try:
            preparation._strict_json(raw)
        except preparation.PrototypePreparationError:
            pass
        else:
            raise AssertionError(f"strict JSON unexpectedly accepted {raw!r}")


def test_external_bindings_are_exact_reviewed_git_objects() -> None:
    contract = _contract()
    assert set(contract["external_bindings"]) == set(preparation.EXPECTED)
    for relative, (expected_sha, expected_oid, expected_size) in preparation.EXPECTED.items():
        raw = preparation._git_blob(preparation.SOURCE_COMMIT, relative)
        assert _sha256(raw) == expected_sha
        assert len(raw) == expected_size
        assert preparation._git_oid(preparation.SOURCE_COMMIT, relative) == expected_oid
        assert contract["external_bindings"][relative] == {
            "git_blob": expected_oid,
            "path": relative,
            "sha256": expected_sha,
            "size_bytes": expected_size,
        }

    packet = _packet()
    assert packet["v3_acceptance_binding"] == {
        "accepted_review_path": preparation.V3_REVIEW,
        "accepted_review_sha256": preparation.EXPECTED[preparation.V3_REVIEW][0],
        "protocol_bundle_sha256": preparation.EXPECTED[preparation.V3_PROTOCOL][0],
        "readiness_packet_sha256": preparation.EXPECTED[preparation.V3_PACKET][0],
        "registry_migration_execution_readiness_accepted": False,
        "schema_bundle_sha256": preparation.EXPECTED[preparation.V3_SCHEMAS][0],
    }


def test_packet_and_contract_authorize_nothing_before_review() -> None:
    packet = _packet()
    contract = _contract()
    assert packet["source_commit"] == contract["source_commit"] == preparation.SOURCE_COMMIT
    assert packet["scientific_target"] == preparation.SCIENTIFIC_TARGET
    assert packet["maintenance_target"] == preparation.MAINTENANCE_TARGET
    assert packet["packet_target"] == preparation.PACKET_TARGET
    assert packet["review_target_recommended_not_selected"] == preparation.REVIEW_TARGET
    assert packet["execution_target_recommended_not_selected"] == preparation.EXECUTION_TARGET
    assert packet["authorization"]["independent_review_required"] is True
    assert all(
        value is False
        for key, value in packet["authorization"].items()
        if key != "independent_review_required"
    )
    assert all(value is False for value in packet["boundary"].values())
    assert contract["authorization"]["contract_independent_review_required"] is True
    assert all(
        value is False
        for key, value in contract["authorization"].items()
        if key != "contract_independent_review_required"
    )
    assert contract["control_harness_contract"]["execution_complete"] is False
    assert contract["lifecycle"]["current_state"] == (
        "PREPARATION_ONLY_REVIEW_REQUIRED_NOT_SELECTED"
    )
    expected_contract_sha = _sha256(preparation.CONTRACT_PATH.read_bytes())
    assert packet["contract_bundle"]["sha256"] == expected_contract_sha
    assert packet["counts"] == {
        "historical_absence_gate_count": 9,
        "primary_control_count": 52,
        "readiness_control_count": 8,
        "runtime_schema_count": 10,
        "stage_a_distinct_control_count": 58,
        "stage_a_runtime_contract_control_count": 18,
        "stage_a_total_control_count": 76,
        "stage_b_distinct_control_count": 60,
        "future_stage_b_total_control_count": 78,
    }


def test_runtime_schemas_are_closed_draft_202012_and_executable() -> None:
    contract = _contract()
    schemas = contract["runtime_schemas"]
    assert contract["runtime_schema_count"] == len(schemas) == 10
    assert set(schemas) == EXPECTED_RUNTIME_SCHEMAS
    assert len({schema["$id"] for schema in schemas.values()}) == len(schemas)
    for name, schema in schemas.items():
        assert schema["$schema"] == "https://json-schema.org/draft/2020-12/schema"
        validator_for(schema).check_schema(schema)
        for pointer, node in _walk(schema, name):
            if isinstance(node, dict) and node.get("type") == "object":
                assert node.get("additionalProperties") is False, pointer
                assert set(node.get("required", [])) == set(
                    node.get("properties", {})
                ), pointer
    validator_contract = contract["validator_contract"]
    assert validator_contract["json_schema_format_checker_required"] is True
    assert validator_contract["json_schema_validator_constructor"] == (
        "Draft202012Validator(schema, format_checker=FormatChecker())"
    )


def test_runtime_schema_positive_fixtures_and_root_negative_controls() -> None:
    contract = _contract()
    fixtures = _positive_fixtures(contract)
    assert set(fixtures) == set(contract["runtime_schemas"])
    for name, fixture in fixtures.items():
        schema = contract["runtime_schemas"][name]
        validator = _validator(schema)
        validator.validate(fixture)

        extra = deepcopy(fixture)
        extra["unexpected"] = True
        assert not validator.is_valid(extra), name

        required = next(
            node["required"]
            for _, node in _walk(schema)
            if isinstance(node, dict) and node.get("type") == "object"
        )
        missing = deepcopy(fixture)
        del missing[required[0]]
        assert not validator.is_valid(missing), name

    runtime = deepcopy(fixtures["runtime_run_manifest"])
    runtime["started_at_utc"] = "not-a-date"
    assert not _validator(
        contract["runtime_schemas"]["runtime_run_manifest"]
    ).is_valid(runtime)

    both_envelopes = deepcopy(fixtures["typed_result_envelope"])
    both_envelopes.update(
        {"exception_type": "ValueError", "message_utf8_base64": "ZXJyb3I="}
    )
    assert not _validator(
        contract["runtime_schemas"]["typed_result_envelope"]
    ).is_valid(both_envelopes)


def test_execution_authority_is_external_and_preflight_binds_implementation() -> None:
    contract = _contract()
    anchor_schema = contract["runtime_schemas"]["reviewed_trust_anchors"]
    authorization = anchor_schema["properties"]["prototype_execution_authorization"]
    assert authorization["additionalProperties"] is False
    assert authorization["properties"]["independent_review_path"]["const"] == (
        preparation.PACKET_REVIEW_PATH
    )
    assert authorization["properties"]["bounded_stage_a_authorized"]["const"] is True
    assert authorization["properties"]["stage_b_authorized"]["const"] is False
    assert authorization["properties"]["anchor_source"]["const"] == (
        "GIT_COMMIT_VERIFIED_INDEPENDENT_REVIEW"
    )
    assert anchor_schema["properties"]["candidate_supplied_values_authoritative"][
        "const"
    ] is False
    api = contract["canonical_interface_and_adapter_contract"]
    assert api[
        "reviewed_trust_anchors_are_loaded_from_git_verified_review_not_candidate_tree"
    ] is True

    preflight = contract["execution_preflight_contract"]
    assert all(preflight.values())
    schema = contract["runtime_schemas"]["execution_preflight"]["properties"]
    assert schema["authorization_review_is_ancestor_of_implementation"]["const"] is True
    assert schema["head_main_origin_equal_implementation_commit"]["const"] is True
    assert schema["main_equals_origin_main"]["const"] is True
    assert schema["worktree_clean"]["const"] is True
    assert schema["historical_record_count"]["const"] == 4691
    assert schema["baseline_classified_consumer_path_count"]["const"] == 496
    assert schema["current_consumer_path_count"]["minimum"] == 496


def test_runtime_schema_artifact_mapping_is_total_and_unambiguous() -> None:
    contract = _contract()
    mapping = contract["runtime_schema_artifact_mapping"]
    assert set(mapping) == set(contract["runtime_schemas"])
    standalone = [row["path"] for row in mapping.values() if row["disposition"] == "STANDALONE"]
    assert len(standalone) == len(set(standalone))
    allowed = set(
        contract["allowed_and_prohibited_paths"][
            "runtime_artifact_paths_relative_to_exact_run_root"
        ].values()
    )
    assert set(standalone) <= allowed
    assert mapping["typed_result_envelope"] == {
        "disposition": "IN_MEMORY_ONLY",
        "feeds_artifact": "runtime_shadow_trace",
        "feeds_fields": ["legacy_result_sha256", "candidate_result_sha256"],
    }
    assert mapping["stage_a_acceptance_binding"] == {
        "disposition": "DEFERRED_SUCCESSOR_ONLY",
        "external_path": preparation.STAGE_A_REVIEW_PATH,
        "external_source_required": "INDEPENDENT_STAGE_A_REVIEW_IN_GIT",
    }
    envelope = contract["typed_result_envelope_validation"]
    assert envelope["persistence"] == "IN_MEMORY_ONLY"
    assert envelope["trace_persists_only_envelope_hashes_in_v3_closed_fields"] == [
        "legacy_result_sha256",
        "candidate_result_sha256",
    ]
    assert envelope["v3_runtime_shadow_trace_schema_is_not_extended"] is True


def test_candidate_payload_is_stable_and_excludes_stage_evidence() -> None:
    contract = _contract()["artifact_source_and_candidate_tree_contract"]
    assert set(contract["candidate_payload_kinds"]) == {
        "CURRENT_PROJECTION",
        "CUSTODY_PAYLOAD",
        "HISTORY_INDEX",
        "HISTORY_SHARD",
    }
    assert "CONSUMER_SOURCE_MAP" not in contract["candidate_payload_kinds"]
    assert "CUSTODY_MANIFEST" not in contract["candidate_payload_kinds"]
    assert contract[
        "consumer_source_map_and_custody_manifest_are_stage_evidence_not_candidate_payload"
    ] is True
    assert contract["candidate_tree_is_independent_of_run_id_and_stage_reports"] is True
    assert contract["compatibility_reconstruction_is_transient_and_removed_after_result_binding"] is True
    assert contract["stage_b_candidate_comparison_semantics_deferred_to_versioned_successor"] is True
    assert contract["candidate_provided_roots_are_recomputed_not_trusted"] is True


def test_control_inventory_error_binding_and_isolation_are_exact() -> None:
    harness = _contract()["control_harness_contract"]
    primary = harness["primary_controls"]
    readiness = harness["readiness_controls"]
    primary_ids = [row["control_id"] for row in primary]
    readiness_ids = [row["control_id"] for row in readiness]
    assert set(primary_ids) == {f"REGISTRY-V1-NC-{index:03d}" for index in range(1, 53)}
    assert set(readiness_ids) == {
        f"REGISTRY-READINESS-V1-RC-{index:03d}" for index in range(1, 9)
    }
    assert len(set(primary_ids + readiness_ids)) == 60
    error_map = harness["control_error_map"]
    assert set(error_map) == set(primary_ids + readiness_ids)
    assert _sha256(preparation.compact_json_bytes(error_map)) == (
        harness["control_error_map_sha256"]
    )
    for row in primary + readiness:
        assert row["expected_decision"] == "REJECT"
        assert row["expected_exact_error_set"] == [error_map[row["control_id"]]]
        assert row["baseline_candidate_recreated_before_mutation"] is True
        assert row["subsequent_controls_receive_unmodified_baseline"] is True
        expected_isolation = (
            "FRESH_TEMPORARY_CANDIDATE_TREE"
            if row in primary
            else "FRESH_IMMUTABLE_ARTIFACT_OVERLAY"
        )
        assert row["fixture_isolation"] == expected_isolation
    assert {row["execution_status"] for row in primary} == {
        "NOT_EXECUTED_PREPARATION_ONLY"
    }
    assert {row["execution_status"] for row in readiness} == {
        "NOT_EXECUTED_CORRECTIVE_PREPARATION_ONLY"
    }


def test_stage_a_partition_and_exact_control_result_schema_are_closed() -> None:
    contract = _contract()
    lifecycle = contract["lifecycle"][
        "stage_a_precutover_execution_after_separate_authorization"
    ]
    expected_primary = [
        row["control_id"]
        for row in contract["control_harness_contract"]["primary_controls"]
        if row["control_id"] != "REGISTRY-V1-NC-044"
    ]
    expected_readiness = [
        row["control_id"]
        for row in contract["control_harness_contract"]["readiness_controls"]
        if row["control_id"] != "REGISTRY-READINESS-V1-RC-001"
    ]
    assert lifecycle["primary_control_ids"] == expected_primary
    assert lifecycle["readiness_control_ids"] == expected_readiness
    assert lifecycle["control_result_order"] == expected_primary + expected_readiness
    assert lifecycle["primary_control_count"] == 51
    assert lifecycle["readiness_control_count"] == 7
    assert lifecycle["distinct_control_count"] == 58
    assert lifecycle["cutover_control_ids_excluded"] == [
        "REGISTRY-V1-NC-044",
        "REGISTRY-READINESS-V1-RC-001",
    ]
    assert set(lifecycle["cutover_control_exclusion_reasons"]) == set(
        lifecycle["cutover_control_ids_excluded"]
    )
    assert lifecycle["final_all_controls_passed_harness_report_allowed"] is False
    assert lifecycle["outputs_require_independent_review"] is True

    results_schema = contract["runtime_schemas"]["stage_a_precutover_report"][
        "properties"
    ]["control_results"]
    assert results_schema["items"] is False
    assert results_schema["minItems"] == results_schema["maxItems"] == 58
    assert len(results_schema["prefixItems"]) == 58
    for expected_id, row_schema in zip(
        lifecycle["control_result_order"], results_schema["prefixItems"], strict=True
    ):
        props = row_schema["properties"]
        assert props["control_id"]["const"] == expected_id
        assert props["expected_decision"]["const"] == "REJECT"
        assert props["observed_decision"]["const"] == "REJECT"
        assert props["passed"]["const"] is True


def test_runtime_contract_validators_and_negative_controls_are_exact() -> None:
    contract = _contract()
    runtime = contract["runtime_validator_contract"]
    assert runtime["entrypoint_count"] == len(runtime["entrypoints"]) == 11
    assert runtime["negative_control_count"] == len(runtime["negative_controls"]) == 18
    assert [row["control_id"] for row in runtime["negative_controls"]] == [
        f"RUNTIME-NC-{index:03d}" for index in range(1, 19)
    ]
    assert runtime["error_precedence"] == preparation.RUNTIME_ERROR_PRECEDENCE
    assert all(row["fresh_baseline"] for row in runtime["negative_controls"])
    assert all(row["subsequent_controls_unmodified"] for row in runtime["negative_controls"])
    assert runtime["stage_a_control_results_root_is_recomputed"] is True
    assert runtime["each_stage_a_positive_baseline_must_pass_before_mutation"] is True
    assert runtime[
        "each_stage_a_baseline_before_and_after_must_equal_report_candidate_tree"
    ] is True
    stage_a = contract["lifecycle"][
        "stage_a_precutover_execution_after_separate_authorization"
    ]
    assert stage_a["runtime_contract_control_count"] == 18
    assert stage_a["total_stage_a_control_count"] == 76
    result_schema = contract["runtime_schemas"]["stage_a_precutover_report"][
        "properties"
    ]["runtime_contract_control_results"]
    assert result_schema["minItems"] == result_schema["maxItems"] == 18
    assert len(result_schema["prefixItems"]) == 18


def test_stage_b_requires_external_stage_a_acceptance_and_reruns_all_controls() -> None:
    lifecycle = _contract()["lifecycle"]
    stage_zero = lifecycle["stage_0_packet_review"]
    assert stage_zero["accepted_review_may_authorize_only"] == preparation.EXECUTION_TARGET
    assert stage_zero["accepted_review_may_authorize_stage_a_only"] is True
    assert stage_zero[
        "stage_b_requires_versioned_successor_after_independent_stage_a_acceptance"
    ] is True
    stage_b = lifecycle["stage_b_full_harness_deferred_obligation"]
    assert stage_b["authorized_or_executable_under_this_contract"] is False
    assert stage_b["versioned_successor_packet_and_independent_review_required"] is True
    assert stage_b["accepted_stage_a_object_is_supplied_from_independently_reviewed_git_binding"] is True
    assert stage_b["candidate_nested_acceptance_is_compared_byte_for_byte_to_external_binding"] is True
    assert stage_b["candidate_may_not_supply_or_rebind_stage_a_acceptance_authority"] is True
    assert stage_b[
        "candidate_comparison_and_dynamic_evidence_pointer_semantics_must_be_resolved_by_successor"
    ] is True
    assert stage_b["rerun_all_controls_in_fresh_overlays"] is True
    assert stage_b["primary_control_count"] == 52
    assert stage_b["readiness_control_count"] == 8
    assert stage_b["distinct_control_count"] == 60
    assert stage_b["effective_profile_invocation_count"] == 199
    assert lifecycle["future_stage_b_review_boundary"][
        "migration_cutover_or_authority_still_not_authorized"
    ] is True


def test_validator_profile_prefix_closure_and_invocation_count_are_derived() -> None:
    harness = _contract()["control_harness_contract"]
    primary = harness["primary_controls"]
    composition = harness["profile_composition"]
    direct = Counter(row["validator_profile"] for row in primary)
    assert direct == Counter(
        {
            "PROTOTYPE_INTEGRITY": 47,
            "WRITE_SAFETY": 2,
            "SHADOW_PARITY": 2,
            "CUTOVER_ELIGIBILITY": 1,
        }
    )
    stage_order = [
        "PROTOTYPE_INTEGRITY",
        "WRITE_SAFETY",
        "SHADOW_PARITY",
        "CUTOVER_ELIGIBILITY",
    ]
    assert composition["stage_order"] == stage_order
    cumulative: list[str] = []
    effective_counts = []
    for profile in stage_order:
        expected_direct = [
            row["control_id"] for row in primary if row["validator_profile"] == profile
        ]
        row = composition["named_entrypoints"][profile]
        assert row["direct_control_ids"] == expected_direct
        cumulative.extend(expected_direct)
        assert row["effective_control_ids"] == cumulative
        assert row["effective_control_count"] == len(cumulative)
        assert row["effective_control_root_sha256"] == _sha256(
            "\n".join(cumulative).encode("utf-8")
        )
        effective_counts.append(len(cumulative))
    assert effective_counts == [47, 49, 51, 52]
    assert sum(effective_counts) == composition["effective_profile_invocation_count"] == 199
    assert composition["candidate_selectable_profile_allowed"] is False
    assert composition["generic_profile_parameter_allowed"] is False


def test_canonical_api_is_single_resolved_read_only_interface() -> None:
    contract = _contract()
    api = contract["canonical_interface_and_adapter_contract"]
    assert api["canonical_anchor_type"] == "ReviewedTrustAnchors"
    assert api["forbidden_unresolved_alias"] == "RegistryTrustAnchors"
    all_entrypoints = api["public_profile_entrypoints"] + api["internal_adapter_entrypoints"]
    assert len(api["public_profile_entrypoints"]) == 4
    assert len(api["internal_adapter_entrypoints"]) == 5
    assert all("RegistryTrustAnchors" not in entrypoint for entrypoint in all_entrypoints)
    assert api["same_public_name_may_not_have_path_and_artifact_source_overloads"] is True
    assert api["all_public_entrypoints_resolve_and_verify_artifact_source_before_validation"] is True
    read_api = contract["read_only_api_contract"]
    assert read_api["entrypoints"] == [
        "load_current_projection()",
        "get_current_target()",
        "get_current_maintenance_target()",
        "get_current_workstream(workstream_id)",
        "get_historical_record(record_id)",
        "iter_historical_records(...)",
        "verify_registry_integrity()",
        "reconstruct_legacy_registry()",
    ]
    assert read_api["new_api_write_entrypoint_exists"] is False
    assert read_api["integrity_verification_bypass_parameter_allowed"] is False
    assert read_api["history_lookup_loads_only_index_selected_shard"] is True


def test_implementation_responsibilities_and_runtime_paths_are_exact() -> None:
    paths = _contract()["allowed_and_prohibited_paths"]
    expected = {
        "formal/python/tools/loop_control_registry_sharding_read_only_prototype_execution.py",
        "formal/python/toe/loop_control_registry_v1.py",
        "formal/python/toe/loop_control_registry_v1_validator.py",
        "formal/python/tests/test_loop_control_registry_v1_production_controls.py",
    }
    assert set(paths["future_tracked_implementation_paths_after_separate_authorization"]) == expected
    assert set(paths["tracked_implementation_responsibility_map"].values()) == expected
    assert paths["runtime_base"] == "formal/scratch/loop_control_registry_v1_prototype"
    assert paths["runtime_write_invariant"] == (
        "ONLY_ALLOWLISTED_PATHS_STRICTLY_WITHIN_EXACT_RESOLVED_RUN_ROOT"
    )


def test_projection_and_shard_contracts_are_closed_and_deterministic() -> None:
    contract = _contract()
    projection = contract["deterministic_projection_contract"]
    assert projection["additional_properties_allowed"] is False
    assert projection["recursive_additional_properties_allowed"] is False
    assert projection["maximum_bytes_exclusive"] == 1_048_576
    assert len(projection["required_top_level_fields"]) == 12
    assert projection["source_mappings"]["maintenance_authority"]["source_sha256"] == (
        preparation.EXPECTED[preparation.MAINTENANCE_AUTHORITY][0]
    )
    assert projection["source_mappings"]["nonpromotion_assertions"][
        "required_source_value"
    ] == "no"

    packing = contract["deterministic_shard_packing_contract"]
    assert packing["input_order"] == (
        "SORT_HISTORY_RECORDS_BY_RECORD_ID_UTF8_BYTEWISE_ASCENDING"
    )
    assert packing["maximum_uncompressed_shard_bytes"] == 5_242_880
    assert packing["oversized_single_record"] == "FAIL_CLOSED"
    assert packing["empty_shards_allowed"] is False
    assert packing["sequence_index_origin"] == 0
    assert packing["maximum_sequence_index"] == 9999
    assert packing["two_independent_regenerations_must_be_byte_identical"] is True
    assert "estimated_shard_count" not in packing

    maximum = packing["maximum_uncompressed_shard_bytes"]

    def pack(rows: list[tuple[str, bytes]]) -> list[bytes]:
        shards: list[bytes] = []
        current = b""
        for _, line in sorted(rows, key=lambda item: item[0].encode("utf-8")):
            if len(line) > maximum:
                raise ValueError("oversized record")
            if current and len(current) + len(line) > maximum:
                shards.append(current)
                current = b""
            current += line
        if current:
            shards.append(current)
        return shards

    prefix = b'{"record_id":"a","value":"'
    suffix = b'"}\n'
    exact = prefix + (b"x" * (maximum - len(prefix) - len(suffix))) + suffix
    small = b'{"record_id":"b"}\n'
    first = pack([("b", small), ("a", exact)])
    second = pack([("a", exact), ("b", small)])
    assert first == second == [exact, small]
    try:
        pack([("x", b"x" * (maximum + 1))])
    except ValueError:
        pass
    else:
        raise AssertionError("oversized single record was accepted")
    assert _sha256(b"a\nb") == _sha256("\n".join(["a", "b"]).encode("utf-8"))


def test_shadow_custody_failure_and_rollback_remain_read_only() -> None:
    contract = _contract()
    shadow = contract["shadow_trace_contract"]
    assert shadow["all_496_static_rows_require_final_disposition"] is True
    assert shadow["baseline_count_is_not_an_eternal_current_count"] is True
    assert shadow["fresh_full_tree_rescan_and_structured_delta_required"] is True
    assert shadow["unobserved_required_consumer_waiver_allowed"] is False
    assert shadow["consumer_migration_or_cutover_during_trace"] is False

    custody = contract["custody_contract"]
    acceptance = custody["execution_procedure"]["acceptance"]
    assert acceptance["byte_identical"] is True
    assert acceptance["decompressed_sha256"] == preparation.EXPECTED[preparation.REGISTRY][0]
    assert acceptance["reconstructed_sha256"] == preparation.EXPECTED[preparation.REGISTRY][0]
    assert acceptance["decompressed_size_bytes"] == 52_340_650
    assert custody["execution_procedure"]["semantic_equivalence_alone_sufficient"] is False
    assert custody["compressed_size_and_sha256_are_realized_execution_values"] is True
    assert custody["reference_compressed_hash_is_non_normative"] is True

    failure = contract["failure_and_rollback"]
    assert failure["failure_may_rotate_target_or_authority"] is False
    assert failure["failure_may_touch_legacy_monolith"] is False
    assert failure["failure_may_touch_scientific_artifacts"] is False
    assert failure["in_place_candidate_repair_after_failure_allowed"] is False
    assert failure["rollback_uses_git_history_rewrite"] is False
    assert failure["rollback_scope"] == (
        "DELETE_ONLY_FILES_CREATED_UNDER_THE_EXACT_RUN_ID_PROTOTYPE_ROOT"
    )


def test_protected_paths_are_unchanged_and_production_layout_is_absent() -> None:
    protected = [
        preparation.REGISTRY,
        preparation.MAINTENANCE_AUTHORITY,
        preparation.AUTHORITATIVE_SURFACES,
        preparation.READINESS_SOURCE,
    ]
    diff = _git("diff", "--name-only", preparation.SOURCE_COMMIT, "--", *protected)
    assert diff.stdout.strip() == ""
    prohibited = set(
        _contract()["allowed_and_prohibited_paths"]["prohibited_runtime_writes"]
    )
    assert set(protected) <= prohibited
    for relative in preparation.FORBIDDEN_TRANSITION_PATHS[:4]:
        assert not (preparation.REPO_ROOT / relative).exists()


def test_historical_absence_transition_binds_all_nine_frozen_trees() -> None:
    transition = _contract()["historical_absence_transition"]
    observed = [(row["gate"], row["commit"]) for row in transition["gates"]]
    assert observed == EXPECTED_HISTORICAL_GATES
    assert transition["gate_count"] == len(observed) == 9
    assert transition["forbidden_paths"] == preparation.FORBIDDEN_TRANSITION_PATHS
    for row in transition["gates"]:
        assert row["all_forbidden_paths_absent"] is True
        assert row["forbidden_path_count"] == len(preparation.FORBIDDEN_TRANSITION_PATHS)
        for relative in preparation.FORBIDDEN_TRANSITION_PATHS:
            assert preparation._path_absent(row["commit"], relative), (
                row["gate"],
                relative,
            )


def test_ten_historical_executable_checks_use_commit_scoped_absence() -> None:
    contract = _contract()
    transition = contract["historical_gate_executable_transition"]
    expected_paths = preparation.CURRENT_WORKTREE_ABSENCE_CHECKS_TO_VERSION
    assert transition["affected_executable_checks"] == expected_paths
    assert transition["per_check_historical_boundary"] == (
        preparation.HISTORICAL_CHECK_BOUNDARIES
    )
    assert transition["performed_as_mechanical_change_in_this_preparation_tranche"] is True
    assert transition["all_existing_integrity_tests_remain_enrolled"] is True
    assert transition["permanently_forbidden_production_authority_paths"] == (
        preparation.FORBIDDEN_TRANSITION_PATHS[:4]
    )
    assert transition["conditionally_allowed_after_accepted_packet_review"] == (
        preparation.FORBIDDEN_TRANSITION_PATHS[4:]
    )
    bindings = contract["historical_absence_transition"][
        "affected_check_source_bindings"
    ]
    assert set(bindings) == set(expected_paths)
    for relative in expected_paths:
        raw = preparation._git_blob(preparation.SOURCE_COMMIT, relative)
        assert bindings[relative] == {
            "git_blob": preparation._git_oid(preparation.SOURCE_COMMIT, relative),
            "sha256": _sha256(raw),
            "size_bytes": len(raw),
        }
        current = (preparation.REPO_ROOT / relative).read_text(encoding="utf-8")
        assert "(REPO_ROOT / relative).exists()" not in current
        assert "(corrective.REPO_ROOT / path).exists()" not in current
        assert "(review.REPO_ROOT / relative).exists()" not in current
        if "/tools/" in relative:
            assert preparation.HISTORICAL_CHECK_BOUNDARIES[relative] in current
            assert "cat-file" in current or "ls-tree" in current
        else:
            assert any(
                token in current
                for token in (
                    "_path_absent",
                    "_git_path_absent",
                    "_path_exists_at_source_commit",
                )
            )


def test_historical_packet_protocol_schema_review_and_lean_bytes_are_unchanged() -> None:
    tracked = _git("ls-tree", "-r", "--name-only", preparation.SOURCE_COMMIT).stdout.splitlines()
    protected_history = [
        path
        for path in tracked
        if (
            path.startswith(
                "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_"
            )
            or path.startswith(
                "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingExecutionReadiness"
            )
        )
    ]
    changed = set(
        _git("diff", "--name-only", preparation.SOURCE_COMMIT, "--", *protected_history)
        .stdout.splitlines()
    )
    assert not changed


def test_preparation_integration_is_complete_without_authority_rotation() -> None:
    relative_test = (
        "formal/python/tests/"
        "test_loop_control_registry_sharding_read_only_prototype_execution_packet.py"
    )
    manifest_path = preparation.REPO_ROOT / (
        "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"
    )
    manifest = _load(manifest_path)
    assert manifest["test_tiers"][relative_test] == "TIER_INTEGRITY"
    integrity = manifest["groups"]["integrity_gates"]
    assert relative_test in integrity["tests"]
    assert integrity["expected_count"] == len(integrity["tests"])
    assert integrity["expected_count"] >= 65
    assert integrity["expected_sha256"] == _sha256(
        "\n".join(integrity["tests"]).encode("utf-8")
    )

    expected_lf_paths = [
        preparation.PACKET_PATH,
        preparation.CONTRACT_PATH,
        Path(preparation.__file__),
        preparation.REPO_ROOT / relative_test,
        preparation.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacket.lean",
    ]
    attributes = (preparation.REPO_ROOT / ".gitattributes").read_text(encoding="utf-8")
    for path in expected_lf_paths:
        relative = path.resolve().relative_to(preparation.REPO_ROOT).as_posix()
        assert f"{relative} text eol=lf" in attributes

    readme = (preparation.REPO_ROOT / "README.md").read_text(encoding="utf-8")
    development = (preparation.REPO_ROOT / "DEVELOPMENT.md").read_text(encoding="utf-8")
    check_command = (
        "formal.python.tools."
        "loop_control_registry_sharding_read_only_prototype_execution_packet --check"
    )
    assert check_command in readme
    assert check_command in development

    lean_path = expected_lf_paths[-1]
    lean = lean_path.read_text(encoding="utf-8")
    assert _sha256(preparation.PACKET_PATH.read_bytes()) in lean
    assert _sha256(preparation.CONTRACT_PATH.read_bytes()) in lean
    assert preparation.SCIENTIFIC_TARGET in lean
    assert preparation.MAINTENANCE_TARGET in lean
    assert "implementationAuthorized : Bool := false" in lean
    assert "prototypeExecutionAuthorized : Bool := false" in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean

    aggregate = (
        preparation.REPO_ROOT / "formal/toe_formal/ToeFormalAll.lean"
    ).read_text(encoding="utf-8")
    assert (
        "import ToeFormal.Release."
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacket"
    ) in aggregate
    assert any(
        f"def trackedModuleCount : Nat := {count}" in aggregate
        for count in (1062, 1063, 1064)
    )
