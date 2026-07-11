from __future__ import annotations

import argparse
import base64
from collections import defaultdict
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any

from jsonschema import Draft202012Validator
from jsonschema.validators import validator_for

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "20a57192305cc794397fdcef06f54cab30c37205"

PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v2.json"
)
SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v2.json"
)
PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v2.json"
)
V1_PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v1.json"
)
V1_REVIEW_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v1.json"
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
    "INDEPENDENT_REVIEW_20260711_v2.json"
)

EXPECTED_SHA256 = {
    PACKET_REL: "7b266614ef80b28595bf617110a18b5853f0171d591d2f43fd2ef06759d82f76",
    SCHEMA_REL: "68dc9a1a3ab9489e84dea59be3b92db1cd0fdc8bc8185338adea007998edb03f",
    PROTOCOL_REL: "38f484e16d3fb87fcfe99df4cd92a66d538ff748d8abc9e78d8600955a480e22",
    V1_REVIEW_REL: "54621eb5c109215ce7737e25cce37d8182256a6832fe186283df49d6b8125d4f",
    CONSUMER_REL: "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
    REGISTRY_REL: "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
    MAINTENANCE_REL: "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
    AUTHORITY_REL: "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
    REQUIREMENTS_REL: "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
}

EXPECTED_GIT_BLOBS = {
    PACKET_REL: "76c7ebc0d6638fa3baf38a0caf497ddc6032be95",
    SCHEMA_REL: "facc904e5920fcb1049c9e878824c68f8fd6c0de",
    PROTOCOL_REL: "42fac40c600eb891f75622b301766b68dc73ccc0",
    V1_REVIEW_REL: "2438d2e9bb5c46df92d8acdc869e483164471ce8",
    CONSUMER_REL: "9f9846ba735813c5b2b18f7a0115d88230a36600",
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

FORBIDDEN_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/scratch/loop_control_registry_v1_prototype",
]


class IndependentReviewV2Error(ValueError):
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
        raise IndependentReviewV2Error(f"missing reviewed blob: {relative}")
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
    return (
        subprocess.run(
            ["git", "cat-file", "-e", f"{SOURCE_COMMIT}:{relative}"],
            cwd=REPO_ROOT,
            capture_output=True,
            check=False,
        ).returncode
        != 0
    )


def _strict_json(raw: bytes) -> Any:
    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise IndependentReviewV2Error(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> Any:
        raise IndependentReviewV2Error(f"nonfinite JSON constant: {value}")

    return json.loads(raw, object_pairs_hook=pairs_hook, parse_constant=reject_constant)


def _assert_closed(node: Any, path: str = "$") -> None:
    if isinstance(node, dict):
        if node.get("type") == "object":
            if node.get("additionalProperties") is not False:
                raise IndependentReviewV2Error(f"open object schema: {path}")
            if set(node.get("required", [])) != set(node.get("properties", {})):
                raise IndependentReviewV2Error(f"schema required/property drift: {path}")
        for key, value in node.items():
            _assert_closed(value, f"{path}/{key}")
    elif isinstance(node, list):
        for index, value in enumerate(node):
            _assert_closed(value, f"{path}/{index}")


def _json_pointer_token(value: str) -> str:
    return value.replace("~", "~0").replace("/", "~1")


def _record_commitments() -> dict[str, Any]:
    registry = _strict_json(_git_blob(REGISTRY_REL))
    maintenance = _strict_json(_git_blob(MAINTENANCE_REL))
    root_keys = [key for key in registry if key != "workstreams"]
    records: list[tuple[str, str, str, Any]] = []
    for key in root_keys:
        records.append(("ROOT_FIELD", key, f"/{_json_pointer_token(key)}", registry[key]))
    for index, row in enumerate(registry["workstreams"]):
        logical_key = str(
            row.get("workstream_id")
            or row.get("id")
            or row.get("target")
            or f"anonymous_workstream_{index}"
        )
        records.append(("WORKSTREAM", logical_key, f"/workstreams/{index}", row))

    occurrences: defaultdict[tuple[str, str, str], int] = defaultdict(int)
    ids: list[str] = []
    identity_rows: list[str] = []
    pointers: list[str] = []
    maximum_payload = 0
    for record_class, logical_key, pointer, payload in records:
        payload_raw = compact_json_bytes(payload)
        payload_sha = _sha256(payload_raw)
        maximum_payload = max(maximum_payload, len(payload_raw))
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
        ids.append(record_id)
        identity_rows.append(f"{record_id}:{payload_sha}:{pointer}")
        pointers.append(pointer)

    authority_payload = {
        "active_workstream_sha256": _sha256(
            compact_json_bytes(registry["active_workstreams"][0])
        ),
        "legacy_current_projection": registry["current_projection_v0"],
        "maintenance_authority": maintenance,
    }
    return {
        "authority_commitment_sha256": _sha256(compact_json_bytes(authority_payload)),
        "full_record_identity_root_sha256": _sha256(
            "\n".join(sorted(ids)).encode("utf-8")
        ),
        "identity_payload_pointer_root_sha256": _sha256(
            "\n".join(sorted(identity_rows)).encode("utf-8")
        ),
        "maximum_canonical_payload_bytes": maximum_payload,
        "original_pointer_set_sha256": _sha256(
            "\n".join(sorted(pointers)).encode("utf-8")
        ),
        "root_field_record_count": len(root_keys),
        "total_record_count": len(ids),
        "workstream_record_count": len(registry["workstreams"]),
    }


def _review_probes() -> dict[str, Any]:
    packet = _strict_json(_git_blob(PACKET_REL))
    schemas = _strict_json(_git_blob(SCHEMA_REL))
    protocol = _strict_json(_git_blob(PROTOCOL_REL))
    v1_protocol = _strict_json(_git_blob(V1_PROTOCOL_REL))
    v1_review = _strict_json(_git_blob(V1_REVIEW_REL))
    consumers = _strict_json(_git_blob(CONSUMER_REL))

    for name, schema in schemas["schemas"].items():
        validator_for(schema).check_schema(schema)
        _assert_closed(schema, name)

    consumer_path_schema = schemas["schemas"]["consumer_source_map"]["properties"][
        "consumers"
    ]["items"]["properties"]["path"]
    consumer_path_validator = Draft202012Validator(consumer_path_schema)
    rejected_consumers = [
        row["path"]
        for row in consumers["consumers"]
        if not consumer_path_validator.is_valid(row["path"])
    ]
    if len(consumers["consumers"]) != 496 or rejected_consumers:
        raise IndependentReviewV2Error(
            f"v2 consumer path round trip failed: {rejected_consumers}"
        )

    issue_schema = protocol["production_validator_interface"]["error_result"]
    validation_issue_schema = schemas["schemas"]["validation_report"]["oneOf"][1][
        "properties"
    ]["issues"]["items"]
    if issue_schema != validation_issue_schema:
        raise IndependentReviewV2Error("issue schemas are not shared exactly")
    issue_validator = Draft202012Validator(issue_schema)
    valid_issue_base = {
        "artifact_path": "validation/report.json",
        "error_code": "V1-E-PROBE",
        "json_pointer": "/probe",
        "message": "probe",
    }
    for control_id in ["REGISTRY-V1-NC-001", "REGISTRY-READINESS-V1-RC-001"]:
        if not issue_validator.is_valid({**valid_issue_base, "control_id": control_id}):
            raise IndependentReviewV2Error(f"issue interface rejects {control_id}")
    mismatched_issue_pair = {
        **valid_issue_base,
        "control_id": "REGISTRY-READINESS-V1-RC-001",
        "error_code": "V1-E-HISTORY-PAYLOAD-BASE64",
    }
    issue_schema_accepts_mismatched_control_error_pair = issue_validator.is_valid(
        mismatched_issue_pair
    )
    if not issue_schema_accepts_mismatched_control_error_pair:
        raise IndependentReviewV2Error("issue control/error mismatch probe drift")
    rejected_prototype_paths = [
        "/absolute/report.json",
        "//server/share/report.json",
        "../report.json",
        "validation/../report.json",
        "validation\\report.json",
    ]
    for path in rejected_prototype_paths:
        if issue_validator.is_valid(
            {**valid_issue_base, "artifact_path": path, "control_id": None}
        ):
            raise IndependentReviewV2Error(f"prototype path false accept remains: {path}")

    original_controls = v1_protocol["typed_control_harness"]["controls"]
    controls = protocol["typed_control_harness"]["controls"]
    if controls != original_controls or len(controls) != 52:
        raise IndependentReviewV2Error("original 52 controls changed")

    composition = protocol["validator_profile_composition"]
    expected_profile_counts = {
        "PROTOTYPE_INTEGRITY": 47,
        "WRITE_SAFETY": 49,
        "SHADOW_PARITY": 51,
        "CUTOVER_ELIGIBILITY": 52,
    }
    for profile, count in expected_profile_counts.items():
        row = composition["named_entrypoints"][profile]
        if row["effective_control_count"] != count:
            raise IndependentReviewV2Error(f"profile count drift: {profile}")
        root = _sha256("\n".join(row["effective_control_ids"]).encode("utf-8"))
        if row["effective_control_root_sha256"] != root:
            raise IndependentReviewV2Error(f"profile root drift: {profile}")

    regressions = protocol["typed_control_harness"]["readiness_regressions"]
    required_metadata = {
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
        "requires_runtime_trace",
        "requires_write_sandbox",
        "subsequent_controls_receive_unmodified_baseline",
        "validator_entrypoint",
        "validator_profile",
    }
    if len(regressions) != 8:
        raise IndependentReviewV2Error("readiness regression count drift")
    for row in regressions:
        if not required_metadata.issubset(row):
            raise IndependentReviewV2Error(f"regression metadata missing: {row['control_id']}")
        if len(row["mutation_matrix"]) != 1 or len(row["expected_exact_error_set"]) != 1:
            raise IndependentReviewV2Error(f"regression is not atomic: {row['control_id']}")

    precedence = protocol["typed_control_harness"]["readiness_error_aggregation"]
    expected_phases = [
        "PROTOTYPE_PATH",
        "PAYLOAD_BASE64",
        "PAYLOAD_ENVELOPE",
        "PAYLOAD_CANONICAL_IDENTITY",
        "PROFILE_CLOSURE",
        "REPORT_INVARIANT",
    ]
    if precedence["error_precedence"] != expected_phases:
        raise IndependentReviewV2Error("readiness error precedence drift")
    if precedence["multiple_errors_for_one_atomic_case_allowed"] is not False:
        raise IndependentReviewV2Error("multiple readiness errors unexpectedly allowed")

    rc2 = next(row for row in regressions if row["control_id"].endswith("RC-002"))
    rc2_case = rc2["mutation_matrix"][0]
    rc2_before_decoded = base64.b64decode(rc2_case["before"], validate=True)
    rc2_after_decoded = base64.b64decode(rc2_case["after"], validate=True)
    if rc2_before_decoded != b"f" or rc2_after_decoded != b"f":
        raise IndependentReviewV2Error("RC-002 decoded-byte probe drift")
    rc2_positive_json_valid = True
    try:
        json.loads(rc2_before_decoded)
    except (json.JSONDecodeError, UnicodeDecodeError):
        rc2_positive_json_valid = False
    if rc2_positive_json_valid:
        raise IndependentReviewV2Error("RC-002 positive fixture unexpectedly became valid JSON")
    recommended_before = "bnVsbA=="
    recommended_after = "bnVsbB=="
    if base64.b64decode(recommended_before, validate=True) != b"null":
        raise IndependentReviewV2Error("recommended RC-002 baseline probe drift")
    if base64.b64decode(recommended_after, validate=True) != b"null":
        raise IndependentReviewV2Error("recommended RC-002 mutation probe drift")
    if base64.b64encode(base64.b64decode(recommended_after, validate=True)).decode(
        "ascii"
    ) != recommended_before:
        raise IndependentReviewV2Error("recommended RC-002 recanonicalization probe drift")

    symbolic_vectors: dict[str, list[Any]] = {}
    for row in regressions:
        values: list[Any] = []
        for case in row["mutation_matrix"]:
            for key in ["before", "after"]:
                value = case[key]
                flattened = json.dumps(value, sort_keys=True)
                if any(
                    token in flattened
                    for token in ["ONE_VALID_ISSUE", "BASELINE_SHA256", "DIFFERENT_SHA256"]
                ):
                    values.append(value)
        if values:
            symbolic_vectors[row["control_id"]] = values
    if set(symbolic_vectors) != {
        "REGISTRY-READINESS-V1-RC-007",
        "REGISTRY-READINESS-V1-RC-008",
    }:
        raise IndependentReviewV2Error("symbolic mutation-vector inventory drift")

    payload_algorithm = protocol["history_payload_validation_algorithm"]
    required_algorithm_fields = {
        "full_record_identity_root_algorithm",
        "identity_payload_pointer_root_algorithm",
        "original_pointer_root_algorithm",
        "record_id_domain_value",
        "record_id_preimage_fields",
        "record_id_preimage_serializer",
        "record_id_result",
    }
    if not required_algorithm_fields.issubset(payload_algorithm):
        raise IndependentReviewV2Error("record/root byte algorithm incomplete")

    shadow = schemas["schemas"]["runtime_shadow_trace_manifest"]
    for field in ["consumer_migration_performed", "cutover_performed"]:
        if shadow["properties"][field] != {"const": False, "type": "boolean"}:
            raise IndependentReviewV2Error(f"shadow attestation drift: {field}")
        if field not in shadow["required"]:
            raise IndependentReviewV2Error(f"shadow attestation optional: {field}")
    shadow_invariants = protocol["success_report_invariants"]["shadow_manifest"]
    for invariant in ["CONSUMER_MIGRATION_PERFORMED_FALSE", "CUTOVER_PERFORMED_FALSE"]:
        if invariant not in shadow_invariants:
            raise IndependentReviewV2Error(f"shadow invariant missing: {invariant}")

    report_contract = protocol["production_validator_interface"]["report_contract"]
    stale_report_term = report_contract.get("passed") == "TRUE_ONLY_WHEN_ERRORS_EMPTY"
    if "errors" in report_contract or "issues" not in report_contract:
        raise IndependentReviewV2Error("report list field correction failed")
    if not stale_report_term:
        raise IndependentReviewV2Error("report terminology probe drift")

    trace_output = protocol["runtime_shadow_tracing_protocol"]["trace_output"]
    trace_output_still_templated = "<run_id>" in trace_output
    if not trace_output_still_templated:
        raise IndependentReviewV2Error("shadow trace-output template probe drift")
    trace_event = schemas["schemas"]["runtime_shadow_trace_event"]
    trace_operations = trace_event["properties"]["operation_type"]["enum"]
    trace_resolved_path_pattern = trace_event["properties"]["resolved_registry_path"][
        "pattern"
    ]
    prototype_path_pattern = protocol["path_type_contract"][
        "PROTOTYPE_ARTIFACT_RELPATH"
    ]["pattern"]
    trace_resolved_path_is_prototype_typed = (
        trace_resolved_path_pattern == prototype_path_pattern
    )
    if "DIRECT_MONOLITH_READ" not in trace_operations:
        raise IndependentReviewV2Error("legacy trace operation disappeared")
    if not trace_resolved_path_is_prototype_typed:
        raise IndependentReviewV2Error("trace path-context probe drift")
    validation_invariants = protocol["success_report_invariants"]["validation_report"]
    issue_control_error_mapping_invariant_present = any(
        "CONTROL" in row and "ERROR" in row for row in validation_invariants
    )
    if issue_control_error_mapping_invariant_present:
        raise IndependentReviewV2Error("issue control/error mapping invariant probe drift")

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
        raise IndependentReviewV2Error("validator dependency closure not directly pinned")

    return {
        "consumers": consumers,
        "packet": packet,
        "protocol": protocol,
        "rc2": {
            "after": rc2_case["after"],
            "after_decoded_utf8": rc2_after_decoded.decode("utf-8"),
            "before": rc2_case["before"],
            "before_decoded_utf8": rc2_before_decoded.decode("utf-8"),
            "positive_fixture_json_valid": rc2_positive_json_valid,
            "recommended_after": recommended_after,
            "recommended_before": recommended_before,
        },
        "record_commitments": _record_commitments(),
        "schemas": schemas,
        "stale_report_term": stale_report_term,
        "issue_schema_accepts_mismatched_control_error_pair": (
            issue_schema_accepts_mismatched_control_error_pair
        ),
        "issue_control_error_mapping_invariant_present": (
            issue_control_error_mapping_invariant_present
        ),
        "symbolic_vectors": symbolic_vectors,
        "trace_resolved_path_is_prototype_typed": (
            trace_resolved_path_is_prototype_typed
        ),
        "trace_output": trace_output,
        "trace_output_still_templated": trace_output_still_templated,
        "v1_review": v1_review,
    }


def build_review() -> dict[str, Any]:
    for path, expected in EXPECTED_SHA256.items():
        if _sha256(_git_blob(path)) != expected:
            raise IndependentReviewV2Error(f"reviewed SHA-256 drift: {path}")
    for path, expected in EXPECTED_GIT_BLOBS.items():
        if _git_blob_oid(path) != expected:
            raise IndependentReviewV2Error(f"reviewed Git blob drift: {path}")

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
        raise IndependentReviewV2Error("record/accounting roots do not reproduce")

    maintenance = _strict_json(_git_blob(MAINTENANCE_REL))
    if maintenance["current_maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewV2Error("maintenance target drift")
    if maintenance["scientific_authority"]["current_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewV2Error("scientific target drift")
    if maintenance["boundary"]["migration_execution_authorized"] is not False:
        raise IndependentReviewV2Error("maintenance authority authorizes migration")
    if packet["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewV2Error("packet scientific target drift")
    if packet["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewV2Error("packet maintenance target drift")
    if any(packet["boundary"].values()):
        raise IndependentReviewV2Error("packet boundary contains execution or promotion")
    if protocol["authorization"]["prototype_artifact_creation_authorized_now"]:
        raise IndependentReviewV2Error("protocol authorizes prototype creation")
    if protocol["authorization"]["registry_migration_execution_authorized"]:
        raise IndependentReviewV2Error("protocol authorizes migration")
    if protocol["authorization"]["registry_cutover_authorized"]:
        raise IndependentReviewV2Error("protocol authorizes cutover")
    if not all(_path_absent_at_commit(path) for path in FORBIDDEN_PATHS):
        raise IndependentReviewV2Error("production or prototype path exists")

    return {
        "accepted_corrections": {
            "all_496_frozen_consumer_paths_validate": True,
            "all_ten_schemas_pass_draft_2020_12_metaschema_and_closure": True,
            "both_control_id_namespaces_validate_in_shared_issue_schema": True,
            "dependency_lock_direct_and_transitive_closure_pinned": True,
            "explicit_shadow_nonmigration_and_noncutover_fields_present": True,
            "original_52_migration_controls_unchanged": True,
            "profile_branches_counts_and_roots_exact": True,
            "prototype_absolute_unc_and_traversal_paths_rejected": True,
            "record_and_root_algorithms_reproduce_frozen_roots": True,
            "v1_error_interface_field_and_id_namespace_defects_structurally_corrected": True,
        },
        "authorization": {
            "corrective_v2_preparation_accepted": False,
            "cutover_authorized": False,
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_rotation_authorized": False,
            "migration_execution_authorized": False,
            "prototype_selection_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_rotation_authorized": False,
            "versioned_v3_required": True,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "custody_and_authority_review": {
            "authority_and_monolith_inputs_bound_to_reviewed_commit": True,
            "forbidden_production_or_prototype_path_count": 0,
            "record_commitments": roots,
            "reviewed_commit": SOURCE_COMMIT,
        },
        "decision": (
            "REJECT_CORRECTIVE_V2_PREPARATION_ACCEPTANCE_RETAIN_AS_HISTORICAL_"
            "CORRECTION_EVIDENCE_REQUIRE_VERSIONED_V3"
        ),
        "findings": [
            {
                "finding_id": "REGISTRY-READINESS-V2-REVIEW-001",
                "packet_defect": True,
                "probe": evidence["rc2"],
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_V2_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "RC-002 declares Zg== as the positive history-payload fixture, but it "
                    "decodes to ASCII f, which is not valid JSON and therefore cannot pass "
                    "the mandatory strict JSON/canonical positive baseline before mutation. "
                    "The exact noncanonical-pad-bit pair should use bnVsbA== to bnVsbB==; "
                    "both decode to JSON null and the latter re-encodes to the former."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V2-REVIEW-002",
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_V2_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "symbolic_mutation_vectors": evidence["symbolic_vectors"],
                "summary": (
                    "RC-007 and RC-008 still use unresolved symbolic mutation values "
                    "(ONE_VALID_ISSUE, BASELINE_SHA256, and DIFFERENT_SHA256). No resolver "
                    "or concrete bytes are frozen, so the claimed exact executable mutation "
                    "matrices and singleton decisions cannot be independently reproduced."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V2-REVIEW-003",
                "packet_defect": True,
                "severity": "MEDIUM",
                "stale_passed_contract": "TRUE_ONLY_WHEN_ERRORS_EMPTY",
                "status": "OPEN_REQUIRES_VERSIONED_INTERFACE_WORDING_CORRECTION",
                "summary": (
                    "The shared report field is now correctly named issues, but the same "
                    "interface still defines passed as TRUE_ONLY_WHEN_ERRORS_EMPTY. This "
                    "retains the rejected field vocabulary inside the frozen contract."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V2-REVIEW-004",
                "packet_defect": True,
                "severity": "MEDIUM",
                "status": "OPEN_REQUIRES_VERSIONED_SHADOW_OUTPUT_CORRECTION",
                "trace_output": evidence["trace_output"],
                "summary": (
                    "The v2 prototype-path contract removes run-ID templates and freezes "
                    "run-root-relative artifact paths, but runtime_shadow_tracing_protocol "
                    "still carries the v0 <run_id> trace-output template."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V2-REVIEW-005",
                "issue_schema_accepts_mismatched_control_error_pair": evidence[
                    "issue_schema_accepts_mismatched_control_error_pair"
                ],
                "mapping_invariant_present": evidence[
                    "issue_control_error_mapping_invariant_present"
                ],
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_V2_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "The shared issue schema accepts either control-ID namespace and any "
                    "V1-E code independently, but neither the schema nor success invariants "
                    "bind each control ID to its frozen exact error code. A schema-valid "
                    "RC-001 issue carrying RC-002's error code therefore passes."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V2-REVIEW-006",
                "packet_defect": True,
                "resolved_registry_path_is_prototype_typed": evidence[
                    "trace_resolved_path_is_prototype_typed"
                ],
                "severity": "MEDIUM",
                "status": "OPEN_REQUIRES_VERSIONED_TRACE_PATH_CONTEXT_CORRECTION",
                "summary": (
                    "The trace event includes DIRECT_MONOLITH_READ but types "
                    "resolved_registry_path and write_paths as prototype-artifact paths "
                    "whose semantic contract requires containment under the run root. "
                    "The protocol does not freeze a field map that can represent observed "
                    "legacy repository paths separately from candidate write paths."
                ),
            },
        ],
        "packet_sha256": EXPECTED_SHA256[PACKET_REL],
        "protocol_sha256": EXPECTED_SHA256[PROTOCOL_REL],
        "recommended_v3_correction": {
            "authority_change_allowed": False,
            "rc002_after": "bnVsbB==",
            "rc002_before": "bnVsbA==",
            "replace_all_symbolic_mutation_values_with_concrete_json_values": True,
            "report_passed_contract": "TRUE_ONLY_WHEN_ISSUES_EMPTY",
            "issue_control_id_error_code_pairs_must_match_frozen_controls": True,
            "shadow_trace_path_fields_require_explicit_repository_vs_prototype_types": True,
            "shadow_trace_output_must_use_frozen_run_root_relative_path": True,
        },
        "review_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v2"
        ),
        "schema_bundle_sha256": EXPECTED_SHA256[SCHEMA_REL],
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v2"
        ),
        "status": (
            "REJECTED_CORRECTIVE_V2_PREPARATION_CONTRACT_INVALID_POSITIVE_FIXTURE_"
            "NONCONCRETE_MUTATION_VECTORS_AND_ISSUE_MAPPING_NO_EXECUTION_OR_AUTHORITY"
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
        description="Build or verify the independent corrective readiness-v2 review."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise IndependentReviewV2Error("corrective readiness-v2 review artifact drift")
        print(f"corrective_readiness_v2_review: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"corrective_readiness_v2_review: wrote {OUTPUT_PATH} sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
