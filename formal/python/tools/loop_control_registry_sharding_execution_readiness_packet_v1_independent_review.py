from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from jsonschema import Draft202012Validator
from jsonschema.validators import validator_for

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "e2af09bbb4355604eee4566707afd3407ed6c4b9"

PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v1.json"
)
SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v1.json"
)
PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v1.json"
)
V0_SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v0.json"
)
V0_PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v0.json"
)
V0_REVIEW_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)
CONSUMER_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
REGISTRY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_REL = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
AUTHORITY_REL = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
REQUIREMENTS_REL = "requirements.ci.lock"

OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v1.json"
)

EXPECTED_SHA256 = {
    PACKET_REL: "ba7275826efe754c9cdc611df32fdc4ea257017d826757de0e63206299db0261",
    SCHEMA_REL: "11b6f870fd57dbc2f325d3aaa9dc5d99e4c1da303e3cee3db182f6e29f020d55",
    PROTOCOL_REL: "4cb61f06e95db05593a1d9918408ceaa0cbfcc503d3720c50a8c5816781c5014",
    V0_SCHEMA_REL: "24f1f2703d9c6c2510b314d132bfdfc09ab9f6207d209bc2620eed328e176a58",
    V0_PROTOCOL_REL: "90a609f6d2be11be94b8c03ea04b1d58452a6f9b9fa26d227383fbfece195c8e",
    V0_REVIEW_REL: "7361b386c68590e776b4dcf354264c3ac07217d8dbabe56f722e8cb5c2b97982",
    CONSUMER_REL: "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
    REGISTRY_REL: "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
    MAINTENANCE_REL: "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
    AUTHORITY_REL: "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
    REQUIREMENTS_REL: "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
}

EXPECTED_GIT_BLOBS = {
    PACKET_REL: "4030d4be7c10ad1a72b900e068a56904b7e4f423",
    SCHEMA_REL: "ab845f6402be57a18c3d1459a8d0557c88c7934a",
    PROTOCOL_REL: "9e722c3e47977b167a6e784a779d10b3f69e75e2",
    REGISTRY_REL: "e6c5b3773dccd92fde9c0a8d486a56f993d6b235",
    MAINTENANCE_REL: "dca311d6abe38a872495c07f302d13ad886c0232",
    AUTHORITY_REL: "d46c5fb1966dcefc6b923776b7d94c4f5009b889",
    REQUIREMENTS_REL: "bcc393883b90739408ed14d53d57dd0b42d0c2bd",
}

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)

AUTHORITY_COMMITMENT_SHA256 = "fd4348411236648d6216900eced59524b87c561bfa0d36186cf4c4d19a2e6b34"
RECORD_IDENTITY_ROOT_SHA256 = "67a23fda6348a2a6e12e4c2af775d115c692ecbe4d0650f0844a982d869e112d"
IDENTITY_PAYLOAD_POINTER_ROOT_SHA256 = (
    "a97799ea412006dde3c259b718b10aad9dee7012181611f3f1d5f1a1e821a967"
)
ORIGINAL_POINTER_ROOT_SHA256 = (
    "219f4bc866b731b74ef50a439b6a869d8add33c6c5ce8e83a621115c1649c6bf"
)

EXPECTED_READINESS_REGRESSIONS = [
    (
        "REGISTRY-READINESS-V1-RC-001",
        "cutover_profile_omits_required_ordered_closure",
        "V1-E-READINESS-PROFILE-CLOSURE",
    ),
    (
        "REGISTRY-READINESS-V1-RC-002",
        "history_payload_invalid_or_noncanonical_base64",
        "V1-E-HISTORY-PAYLOAD-BASE64",
    ),
    (
        "REGISTRY-READINESS-V1-RC-003",
        "history_payload_declared_size_hash_or_kind_disagrees",
        "V1-E-HISTORY-PAYLOAD-ENVELOPE",
    ),
    (
        "REGISTRY-READINESS-V1-RC-004",
        "history_payload_noncanonical_json_or_rebound_record_id",
        "V1-E-HISTORY-PAYLOAD-CANONICAL-IDENTITY",
    ),
    (
        "REGISTRY-READINESS-V1-RC-005",
        "prototype_path_is_posix_absolute",
        "V1-E-PATH-POSIX-ABSOLUTE",
    ),
    (
        "REGISTRY-READINESS-V1-RC-006",
        "prototype_path_is_slash_unc",
        "V1-E-PATH-SLASH-UNC",
    ),
    (
        "REGISTRY-READINESS-V1-RC-007",
        "validation_report_passes_with_nonempty_issues",
        "V1-E-VALIDATION-REPORT-INVARIANT",
    ),
    (
        "REGISTRY-READINESS-V1-RC-008",
        "harness_success_has_mismatched_hashes_or_profile_counts",
        "V1-E-HARNESS-REPORT-INVARIANT",
    ),
]

FORBIDDEN_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/scratch/loop_control_registry_v1_prototype",
]


class IndependentReviewError(ValueError):
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


def _git_blob(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise IndependentReviewError(f"missing reviewed blob: {relative}")
    return result.stdout


def _git_blob_oid(relative: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _path_absent_at_commit(relative: str) -> bool:
    result = subprocess.run(
        ["git", "cat-file", "-e", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    return result.returncode != 0


def _strict_json(raw: bytes) -> Any:
    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise IndependentReviewError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> Any:
        raise IndependentReviewError(f"nonfinite JSON constant: {value}")

    return json.loads(raw, object_pairs_hook=pairs_hook, parse_constant=reject_constant)


def _assert_recursively_closed(node: Any, path: str = "$") -> None:
    if isinstance(node, dict):
        if node.get("type") == "object":
            if node.get("additionalProperties") is not False:
                raise IndependentReviewError(f"open object schema: {path}")
            if set(node.get("required", [])) != set(node.get("properties", {})):
                raise IndependentReviewError(f"optional or undeclared property: {path}")
        for key, value in node.items():
            _assert_recursively_closed(value, f"{path}/{key}")
    elif isinstance(node, list):
        for index, value in enumerate(node):
            _assert_recursively_closed(value, f"{path}/{index}")


def _json_pointer_token(value: str) -> str:
    return value.replace("~", "~0").replace("/", "~1")


def _reproduce_record_commitments() -> dict[str, Any]:
    registry = _strict_json(_git_blob(REGISTRY_REL))
    maintenance = _strict_json(_git_blob(MAINTENANCE_REL))
    root_keys = [key for key in registry if key != "workstreams"]
    workstreams = registry["workstreams"]
    records: list[tuple[str, str, str, Any]] = []
    for key in root_keys:
        records.append(("ROOT_FIELD", key, f"/{_json_pointer_token(key)}", registry[key]))
    for index, row in enumerate(workstreams):
        logical_key = str(
            row.get("workstream_id")
            or row.get("id")
            or row.get("target")
            or f"anonymous_workstream_{index}"
        )
        records.append(("WORKSTREAM", logical_key, f"/workstreams/{index}", row))

    occurrences: defaultdict[tuple[str, str, str], int] = defaultdict(int)
    record_ids: list[str] = []
    identity_rows: list[str] = []
    pointers: list[str] = []
    maximum_payload_bytes = 0
    for record_class, logical_key, pointer, payload in records:
        payload_raw = compact_json_bytes(payload)
        payload_sha = _sha256(payload_raw)
        maximum_payload_bytes = max(maximum_payload_bytes, len(payload_raw))
        occurrence_key = (record_class, logical_key, payload_sha)
        ordinal = occurrences[occurrence_key]
        occurrences[occurrence_key] += 1
        preimage = compact_json_bytes(
            {
                "domain": "LOOP_CONTROL_RECORD_ID_v1",
                "identical_occurrence_ordinal": ordinal,
                "logical_key": logical_key,
                "original_json_pointer": pointer,
                "payload_sha256": payload_sha,
                "record_class": record_class,
                "source_git_blob": EXPECTED_GIT_BLOBS[REGISTRY_REL],
                "source_path": REGISTRY_REL,
            }
        )
        record_id = "lcr1:" + _sha256(preimage)
        record_ids.append(record_id)
        identity_rows.append(f"{record_id}:{payload_sha}:{pointer}")
        pointers.append(pointer)

    active_workstream = registry["active_workstreams"][0]
    authority_payload = {
        "active_workstream_sha256": _sha256(compact_json_bytes(active_workstream)),
        "legacy_current_projection": registry["current_projection_v0"],
        "maintenance_authority": maintenance,
    }
    return {
        "authority_commitment_sha256": _sha256(compact_json_bytes(authority_payload)),
        "full_record_identity_root_sha256": _sha256(
            "\n".join(sorted(record_ids)).encode("utf-8")
        ),
        "identity_payload_pointer_root_sha256": _sha256(
            "\n".join(sorted(identity_rows)).encode("utf-8")
        ),
        "maximum_canonical_payload_bytes": maximum_payload_bytes,
        "original_pointer_set_sha256": _sha256(
            "\n".join(sorted(pointers)).encode("utf-8")
        ),
        "root_field_record_count": len(root_keys),
        "total_record_count": len(record_ids),
        "workstream_record_count": len(workstreams),
    }


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


def _review_probes() -> dict[str, Any]:
    packet = _strict_json(_git_blob(PACKET_REL))
    schemas = _strict_json(_git_blob(SCHEMA_REL))
    protocol = _strict_json(_git_blob(PROTOCOL_REL))
    v0_schemas = _strict_json(_git_blob(V0_SCHEMA_REL))
    v0_protocol = _strict_json(_git_blob(V0_PROTOCOL_REL))
    v0_review = _strict_json(_git_blob(V0_REVIEW_REL))
    consumer = _strict_json(_git_blob(CONSUMER_REL))

    for name, schema in schemas["schemas"].items():
        validator_for(schema).check_schema(schema)
        _assert_recursively_closed(schema, name)

    path_schema_v0 = v0_schemas["schemas"]["current_projection"]["properties"][
        "source_legacy_identity"
    ]["properties"]["path"]
    path_schema_v1 = schemas["schemas"]["current_projection"]["properties"][
        "source_legacy_identity"
    ]["properties"]["path"]
    path_v0 = Draft202012Validator(path_schema_v0)
    path_v1 = Draft202012Validator(path_schema_v1)
    rejected_v0_false_accepts = ["/tmp/registry.json", "//server/share/registry.json"]
    if not all(path_v0.is_valid(value) for value in rejected_v0_false_accepts):
        raise IndependentReviewError("v0 path false-accept probe no longer reproduces")
    if not all(not path_v1.is_valid(value) for value in rejected_v0_false_accepts):
        raise IndependentReviewError("v1 path correction did not reject v0 false accept")

    history_v0 = v0_schemas["schemas"]["history_shard_record"]
    history_v1 = schemas["schemas"]["history_shard_record"]
    invalid_payload_record = {
        "identical_occurrence_ordinal": 0,
        "logical_key": "x",
        "original_json_pointer": "/x",
        "payload_canonical_json_utf8_base64": "!!!!",
        "payload_kind": "NULL",
        "payload_sha256": "0" * 64,
        "payload_size_bytes": 1,
        "record_class": "ROOT_FIELD",
        "record_id": "lcr1:" + "0" * 64,
        "record_version": 1,
        "schema_id": "LOOP_CONTROL_HISTORY_RECORD_v1",
        "source_git_blob": EXPECTED_GIT_BLOBS[REGISTRY_REL],
        "source_path": REGISTRY_REL,
    }
    if not Draft202012Validator(history_v0).is_valid(invalid_payload_record):
        raise IndependentReviewError("v0 invalid-payload false accept no longer reproduces")
    if Draft202012Validator(history_v1).is_valid(invalid_payload_record):
        raise IndependentReviewError("v1 invalid-payload structural correction failed")

    validation_v0 = Draft202012Validator(v0_schemas["schemas"]["validation_report"])
    contradictory_v0 = {
        "candidate_root_sha256": "0" * 64,
        "issues": [
            {
                "artifact_path": "validation/report.json",
                "control_id": None,
                "error_code": "V1-E-TEST",
                "json_pointer": "",
                "message": "probe",
            }
        ],
        "passed": True,
        "profile": "PROTOTYPE_INTEGRITY",
        "schema_id": "LOOP_CONTROL_VALIDATION_REPORT_v1",
        "trust_anchor_sha256": "1" * 64,
    }
    if not validation_v0.is_valid(contradictory_v0):
        raise IndependentReviewError("v0 contradictory-report false accept no longer reproduces")
    validation_v1 = Draft202012Validator(schemas["schemas"]["validation_report"])
    valid_report = _valid_validation_report()
    if not validation_v1.is_valid(valid_report):
        raise IndependentReviewError("v1 positive validation report rejected")
    contradictory_v1 = json.loads(json.dumps(valid_report))
    contradictory_v1["issues"] = [
        {
            "artifact_path": "validation/report.json",
            "control_id": None,
            "error_code": "V1-E-TEST",
            "json_pointer": "",
            "message": "probe",
        }
    ]
    if validation_v1.is_valid(contradictory_v1):
        raise IndependentReviewError("v1 contradictory validation report accepted")

    original_controls = v0_protocol["typed_control_harness"]["controls"]
    corrected_controls = protocol["typed_control_harness"]["controls"]
    if corrected_controls != original_controls or len(corrected_controls) != 52:
        raise IndependentReviewError("original 52-control contract changed")
    readiness_regressions = protocol["typed_control_harness"]["readiness_regressions"]
    observed_regressions = [
        (row["control_id"], row["mutation"], row["expected_exact_error_set"][0])
        for row in readiness_regressions
    ]
    if observed_regressions != EXPECTED_READINESS_REGRESSIONS:
        raise IndependentReviewError("readiness regression controls drift")

    regression_required_execution_metadata = {
        "artifact_kind",
        "baseline_candidate_recreated_before_mutation",
        "fixture_isolation",
        "mutation_precondition",
        "mutator_entrypoint",
        "rebind_candidate_internal_hashes",
        "requires_runtime_trace",
        "requires_write_sandbox",
        "subsequent_controls_receive_unmodified_baseline",
        "validator_profile",
    }
    if not regression_required_execution_metadata.issubset(set(original_controls[0])):
        raise IndependentReviewError("review metadata reference set drift")
    regression_metadata_gaps = {
        row["control_id"]: sorted(regression_required_execution_metadata - set(row))
        for row in readiness_regressions
    }
    if not all(regression_metadata_gaps.values()):
        raise IndependentReviewError("readiness regressions unexpectedly gained full metadata")
    disjunctive_regression_ids = [
        row["control_id"]
        for row in readiness_regressions
        if "_or_" in row["mutation"]
    ]
    if disjunctive_regression_ids != [
        "REGISTRY-READINESS-V1-RC-002",
        "REGISTRY-READINESS-V1-RC-003",
        "REGISTRY-READINESS-V1-RC-004",
        "REGISTRY-READINESS-V1-RC-008",
    ]:
        raise IndependentReviewError("disjunctive readiness-regression inventory drift")

    composition = protocol["validator_profile_composition"]
    expected_profiles = {
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
    for profile, (closure, count) in expected_profiles.items():
        row = composition["named_entrypoints"][profile]
        if row["ordered_closure"] != closure or row["effective_control_count"] != count:
            raise IndependentReviewError(f"profile closure drift: {profile}")
        expected_root = _sha256("\n".join(row["effective_control_ids"]).encode("utf-8"))
        if row["effective_control_root_sha256"] != expected_root:
            raise IndependentReviewError(f"profile root drift: {profile}")
    if "extends" in json.dumps(composition):
        raise IndependentReviewError("ambiguous profile inheritance remains")
    cutover = composition["named_entrypoints"]["CUTOVER_ELIGIBILITY"]
    if cutover["live_legacy_reader_requirement"] != "FORBIDDEN_AT_CUTOVER":
        raise IndependentReviewError("cutover live-reader requirement drift")
    if cutover["shadow_stage_semantics"] != (
        "VERIFY_PREVIOUSLY_ACCEPTED_IMMUTABLE_SHADOW_MANIFEST_NO_LIVE_DUAL_READ"
    ):
        raise IndependentReviewError("cutover shadow-stage resolution drift")

    payload_algorithm = protocol["history_payload_validation_algorithm"]
    required_steps = {
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
    }
    if set(payload_algorithm["mandatory_ordered_steps"]) != required_steps:
        raise IndependentReviewError("history payload semantic algorithm incomplete")

    lock_lines = {
        line.strip()
        for line in _git_blob(REQUIREMENTS_REL).decode("utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#") and not line.startswith("-r ")
    }
    required_lock_lines = {
        "jsonschema==4.26.0",
        "attrs==26.1.0",
        "jsonschema-specifications==2025.9.1",
        "referencing==0.37.0",
        "rpds-py==0.30.0",
        "typing_extensions==4.16.0",
    }
    if not required_lock_lines.issubset(lock_lines):
        raise IndependentReviewError("jsonschema direct/transitive closure is not pinned")
    lock_contract = protocol["validator_engine_and_lock_contract"]
    if lock_contract["direct_requirements_lock_entry_present_at_source_commit"] is not True:
        raise IndependentReviewError("validator direct lock posture drift")
    if lock_contract["transitive_closure_directly_pinned"] is not True:
        raise IndependentReviewError("validator transitive lock posture drift")
    if lock_contract["requirements_lock_sha256"] != EXPECTED_SHA256[REQUIREMENTS_REL]:
        raise IndependentReviewError("validator lock hash drift")

    consumer_path_schema = schemas["schemas"]["consumer_source_map"]["properties"][
        "consumers"
    ]["items"]["properties"]["path"]
    consumer_path_validator = Draft202012Validator(consumer_path_schema)
    incompatible_consumer_paths = sorted(
        row["path"]
        for row in consumer["consumers"]
        if not consumer_path_validator.is_valid(row["path"])
    )
    expected_incompatible = [
        ".gitattributes",
        ".vscode/settings.json",
        "Physics Imps and Sigs.txt",
    ]
    if incompatible_consumer_paths != expected_incompatible:
        raise IndependentReviewError(
            "unexpected corrective consumer-path compatibility result: "
            + repr(incompatible_consumer_paths)
        )

    interface_error_schema = protocol["production_validator_interface"]["error_result"]
    interface_error_path = Draft202012Validator(
        interface_error_schema["properties"]["artifact_path"]
    )
    interface_control_id = Draft202012Validator(
        interface_error_schema["properties"]["control_id"]
    )
    interface_false_accept_paths = [
        value
        for value in ["/tmp/registry.json", "//server/share/registry.json"]
        if interface_error_path.is_valid(value)
    ]
    interface_rejected_readiness_control_ids = [
        control_id
        for control_id, _, _ in EXPECTED_READINESS_REGRESSIONS
        if not interface_control_id.is_valid(control_id)
    ]
    if interface_false_accept_paths != [
        "/tmp/registry.json",
        "//server/share/registry.json",
    ]:
        raise IndependentReviewError("validator interface path false-accept result drift")
    if interface_rejected_readiness_control_ids != [
        row[0] for row in EXPECTED_READINESS_REGRESSIONS
    ]:
        raise IndependentReviewError("validator interface control-id incompatibility drift")

    report_contract = protocol["production_validator_interface"]["report_contract"]
    validation_report_properties = set(
        schemas["schemas"]["validation_report"]["oneOf"][0]["properties"]
    )
    report_contract_schema_name_mismatch = (
        "errors" in report_contract
        and "errors" not in validation_report_properties
        and "issues" in validation_report_properties
    )
    if not report_contract_schema_name_mismatch:
        raise IndependentReviewError("validator report-contract/schema mismatch result drift")

    required_identity_algorithm_fields = {
        "record_id_domain_value",
        "record_id_preimage_serializer",
        "full_record_identity_root_algorithm",
        "identity_payload_pointer_root_algorithm",
        "original_pointer_root_algorithm",
    }
    missing_identity_algorithm_fields = sorted(
        required_identity_algorithm_fields - set(payload_algorithm)
    )
    if missing_identity_algorithm_fields != sorted(required_identity_algorithm_fields):
        raise IndependentReviewError("record identity algorithm completeness result drift")

    shadow_schema_properties = set(
        schemas["schemas"]["runtime_shadow_trace_manifest"]["properties"]
    )
    missing_shadow_attestations = sorted(
        {"consumer_migration_performed", "cutover_performed"}
        - shadow_schema_properties
    )
    if missing_shadow_attestations != [
        "consumer_migration_performed",
        "cutover_performed",
    ]:
        raise IndependentReviewError("shadow attestation completeness result drift")
    shadow_invariants = protocol["success_report_invariants"]["shadow_manifest"]
    if any("CUTOVER" in row for row in shadow_invariants):
        raise IndependentReviewError("shadow invariant unexpectedly gained cutover attestation")

    return {
        "consumer": consumer,
        "disjunctive_regression_ids": disjunctive_regression_ids,
        "incompatible_consumer_paths": incompatible_consumer_paths,
        "interface_false_accept_paths": interface_false_accept_paths,
        "interface_rejected_readiness_control_ids": (
            interface_rejected_readiness_control_ids
        ),
        "missing_identity_algorithm_fields": missing_identity_algorithm_fields,
        "missing_shadow_attestations": missing_shadow_attestations,
        "packet": packet,
        "protocol": protocol,
        "record_commitments": _reproduce_record_commitments(),
        "regression_metadata_gaps": regression_metadata_gaps,
        "report_contract_schema_name_mismatch": report_contract_schema_name_mismatch,
        "schemas": schemas,
        "v0_review": v0_review,
    }


def build_review() -> dict[str, Any]:
    for path, expected in EXPECTED_SHA256.items():
        if _sha256(_git_blob(path)) != expected:
            raise IndependentReviewError(f"reviewed SHA-256 drift: {path}")
    for path, expected in EXPECTED_GIT_BLOBS.items():
        if _git_blob_oid(path) != expected:
            raise IndependentReviewError(f"reviewed Git blob drift: {path}")

    evidence = _review_probes()
    packet = evidence["packet"]
    protocol = evidence["protocol"]
    roots = evidence["record_commitments"]
    expected_roots = {
        "authority_commitment_sha256": AUTHORITY_COMMITMENT_SHA256,
        "full_record_identity_root_sha256": RECORD_IDENTITY_ROOT_SHA256,
        "identity_payload_pointer_root_sha256": IDENTITY_PAYLOAD_POINTER_ROOT_SHA256,
        "maximum_canonical_payload_bytes": 2_124_270,
        "original_pointer_set_sha256": ORIGINAL_POINTER_ROOT_SHA256,
        "root_field_record_count": 4_152,
        "total_record_count": 4_691,
        "workstream_record_count": 539,
    }
    if roots != expected_roots:
        raise IndependentReviewError("independent record commitment reproduction mismatch")

    maintenance = _strict_json(_git_blob(MAINTENANCE_REL))
    if maintenance["current_maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewError("maintenance target drift")
    if maintenance["scientific_authority"]["current_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewError("scientific target drift")
    if maintenance["boundary"]["migration_execution_authorized"] is not False:
        raise IndependentReviewError("maintenance authority unexpectedly authorizes migration")
    if packet["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewError("packet scientific target drift")
    if packet["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewError("packet maintenance target drift")
    if any(packet["boundary"].values()):
        raise IndependentReviewError("packet boundary contains execution or promotion")
    forbidden_authorization_keys = [
        "prototype_artifact_creation_authorized_now",
        "registry_cutover_authorized",
        "registry_migration_execution_authorized",
    ]
    if any(protocol["authorization"][key] for key in forbidden_authorization_keys):
        raise IndependentReviewError("protocol unexpectedly authorizes execution or cutover")
    if not all(_path_absent_at_commit(path) for path in FORBIDDEN_PATHS):
        raise IndependentReviewError("production or prototype path exists in reviewed commit")

    incompatible = evidence["incompatible_consumer_paths"]
    return {
        "accepted_corrections": {
            "all_ten_schemas_pass_draft_2020_12_metaschema": True,
            "base64_false_accept_rejected_structurally": True,
            "history_payload_base64_and_cross_field_validation_steps_added": True,
            "original_52_migration_controls_byte_semantically_unchanged": True,
            "path_absolute_and_slash_unc_false_accepts_rejected_structurally": True,
            "profile_closures_exact_ordered_and_nonambiguous": True,
            "v0_validation_and_harness_report_contradiction_probes_addressed": True,
            "requirements_direct_and_transitive_validator_closure_pinned": True,
            "eight_readiness_regression_id_mutation_and_error_rows_reproduced": True,
        },
        "authorization": {
            "corrective_v1_preparation_accepted": False,
            "cutover_authorized": False,
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_rotation_authorized": False,
            "migration_execution_authorized": False,
            "prototype_selection_authorized": False,
            "review_successor_required": True,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_rotation_authorized": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "control_review": {
            "distinct_control_count": 60,
            "effective_profile_invocation_count": 199,
            "migration_control_count": 52,
            "readiness_regression_control_count": 8,
        },
        "custody_and_authority_review": {
            "authority_and_monolith_inputs_bound_to_reviewed_commit": True,
            "forbidden_production_or_prototype_path_count": 0,
            "record_commitments": roots,
            "reviewed_commit": SOURCE_COMMIT,
        },
        "decision": (
            "REJECT_CORRECTIVE_V1_PREPARATION_ACCEPTANCE_RETAIN_AS_HISTORICAL_"
            "CORRECTION_EVIDENCE_NO_PROTOTYPE_MIGRATION_OR_CUTOVER"
        ),
        "findings": [
            {
                "finding_id": "REGISTRY-READINESS-V1-REVIEW-001",
                "incompatible_consumer_count": len(incompatible),
                "incompatible_consumer_paths": incompatible,
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_CORRECTIVE_V1_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "The globally substituted repository-path schema rejects three existing "
                    "tracked baseline consumer paths (.gitattributes, .vscode/settings.json, "
                    "and Physics Imps and Sigs.txt), so the corrective consumer-source-map "
                    "schema cannot represent the full 496-row inventory it must reconcile."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V1-REVIEW-002",
                "interface_false_accept_paths": evidence[
                    "interface_false_accept_paths"
                ],
                "interface_rejected_readiness_control_ids": evidence[
                    "interface_rejected_readiness_control_ids"
                ],
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_CORRECTIVE_V1_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "The production-validator error-result interface retains the rejected "
                    "v0 path schema and NC-only control-ID grammar: it accepts POSIX absolute "
                    "and slash-UNC artifact paths and cannot represent any of the eight new "
                    "REGISTRY-READINESS-V1-RC decisions."
                ),
            },
            {
                "disjunctive_regression_ids": evidence[
                    "disjunctive_regression_ids"
                ],
                "finding_id": "REGISTRY-READINESS-V1-REVIEW-003",
                "missing_execution_metadata_by_control": evidence[
                    "regression_metadata_gaps"
                ],
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_CORRECTIVE_V1_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "The eight readiness regression rows omit the executable mutation "
                    "metadata frozen for the original controls. RC-002, RC-003, RC-004, "
                    "and RC-008 also combine multiple mutations with 'or', without exact "
                    "test vectors, atomic-transform rules, or deterministic error precedence, "
                    "so their promised singleton exact-error decisions are not executable."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V1-REVIEW-004",
                "missing_identity_algorithm_fields": evidence[
                    "missing_identity_algorithm_fields"
                ],
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_CORRECTIVE_V1_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "The record-ID and record-root procedure names the preimage fields but "
                    "does not freeze the domain value, exact compact serializer, or byte "
                    "framing/sort/join algorithms for the three externally checked roots. "
                    "Independent implementations can therefore disagree while claiming the "
                    "same named algorithm."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V1-REVIEW-005",
                "packet_defect": True,
                "report_contract_schema_name_mismatch": evidence[
                    "report_contract_schema_name_mismatch"
                ],
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_CORRECTIVE_V1_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "The production-validator report contract still specifies an `errors` "
                    "ordered list while the corrected validation-report schema requires an "
                    "`issues` field and forbids unknown fields, leaving the frozen interface "
                    "and its report schema mutually inconsistent."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V1-REVIEW-006",
                "missing_shadow_attestations": evidence[
                    "missing_shadow_attestations"
                ],
                "packet_defect": True,
                "severity": "MEDIUM",
                "status": "OPEN_REQUIRES_VERSIONED_SHADOW_REPORT_CORRECTION",
                "summary": (
                    "The shadow-success manifest cannot explicitly attest that consumer "
                    "migration and cutover were not performed. The protocol keeps a combined "
                    "precondition false, but the closed result schema lacks both fields and "
                    "the success invariants do not bind a cutover attestation into the report."
                ),
            },
        ],
        "packet_sha256": EXPECTED_SHA256[PACKET_REL],
        "protocol_sha256": EXPECTED_SHA256[PROTOCOL_REL],
        "recommended_successor_correction": {
            "action": (
                "VERSIONED_V2_SPLIT_PROTOTYPE_ARTIFACT_PATHS_FROM_GENERAL_REPOSITORY_"
                "RELATIVE_CONSUMER_PATHS_REPAIR_VALIDATOR_ERROR_INTERFACE_AND_FREEZE_"
                "ATOMIC_READINESS_MUTATION_MATRICES"
            ),
            "authority_change_allowed": False,
            "consumer_paths_must_round_trip": 496,
            "error_interface_must_accept_all_eight_readiness_control_ids": True,
            "prototype_path_schema_remains_strict": True,
            "record_id_and_root_byte_algorithms_must_be_complete": True,
            "readiness_controls_require_atomic_vectors_and_error_precedence": True,
            "report_contract_and_schema_field_names_must_match": True,
            "shadow_manifest_must_attest_no_migration_or_cutover": True,
        },
        "review_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v1"
        ),
        "schema_bundle_sha256": EXPECTED_SHA256[SCHEMA_REL],
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v1"
        ),
        "status": (
            "REJECTED_CORRECTIVE_V1_PREPARATION_CONTRACT_INTERFACE_PATH_IDENTITY_"
            "CONTROL_AND_REPORT_DEFECTS_NO_EXECUTION_OR_AUTHORITY"
        ),
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
        description="Build or verify the independent corrective readiness-v1 review."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise IndependentReviewError("corrective readiness-v1 review artifact drift")
        print(f"corrective_readiness_v1_review: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"corrective_readiness_v1_review: wrote {OUTPUT_PATH} sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
