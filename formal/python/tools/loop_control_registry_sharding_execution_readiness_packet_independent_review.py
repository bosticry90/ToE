from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any

from jsonschema import Draft202012Validator

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PREPARATION_COMMIT = "bf8c12918675d77c27c0eadde009134fc572c281"
CORRECTED_REVIEW_BOUNDARY_COMMIT = "a0d44da40922d6547f02241174fa640edb3f9fa8"
ACCEPTED_SOURCE_COMMIT = "6aba59d8d399b331db010f1f5f857075b9100b7f"

PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v0.json"
)
SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v0.json"
)
PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v0.json"
)
PREPARATION_GENERATOR_REL = (
    "formal/python/tools/"
    "loop_control_registry_sharding_execution_readiness_packet.py"
)
PREPARATION_TEST_REL = (
    "formal/python/tests/"
    "test_loop_control_registry_sharding_execution_readiness_packet.py"
)
PREPARATION_LEAN_REL = (
    "formal/toe_formal/ToeFormal/Release/"
    "LoopControlRegistryShardingExecutionReadinessPacket.lean"
)
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)

V1_PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_"
    "GUARDRAIL_PACKET_20260711_v1.json"
)
V1_REVIEW_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_"
    "GUARDRAIL_INDEPENDENT_REVIEW_20260711_v1.json"
)
V1_CONSUMER_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
V1_CUSTODY_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_LEGACY_BYTE_CUSTODY_CONTRACT_20260711_v1.json"
)
REGISTRY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
AUTHORITY_REL = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
MAINTENANCE_REL = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
PACKET_TARGET = (
    "prepare_loop_control_registry_sharding_execution_readiness_packet_v0"
)

EXPECTED_PREPARATION_SHA256 = {
    PACKET_REL: "ddca270745ebea3659cf9b53aa09c4c0c25a0983101a1d310e1f98380b3874c8",
    SCHEMA_REL: "24f1f2703d9c6c2510b314d132bfdfc09ab9f6207d209bc2620eed328e176a58",
    PROTOCOL_REL: "90a609f6d2be11be94b8c03ea04b1d58452a6f9b9fa26d227383fbfece195c8e",
    PREPARATION_GENERATOR_REL: (
        "e87aa161b4ad91fc7103754582d743255c9642e05daef901c584da60df45a323"
    ),
    PREPARATION_TEST_REL: (
        "eb2e2763302bdeb8ffe90b63be805129cef71147fae55837bcc34b010bbdc869"
    ),
    PREPARATION_LEAN_REL: (
        "de9b9e4057b39613ddb8064d2900c3e5ab05aeb47c342abca703fe01d584385b"
    ),
}
EXPECTED_PREPARATION_GIT_BLOBS = {
    PACKET_REL: "bd1bc805b614b8d6fbcfa293455b7dfdb79dfe47",
    SCHEMA_REL: "94a8a32517a9015b5a968c029b5fd15dd7ef0aba",
    PROTOCOL_REL: "9044bed2b99e8bd327d7ad31f6d7c14a8a131818",
    PREPARATION_GENERATOR_REL: "274b8a508c9803ab37d0d61d770380e1d3ce1853",
    PREPARATION_TEST_REL: "a323c4288688f4f78d7ec7d9e1ab594321d8ae8f",
    PREPARATION_LEAN_REL: "ae5c0ebb699aa6a583a79f19bb7320a0729893fb",
}
EXPECTED_CORRECTED_TEST_SHA256 = (
    "669f5b8f94fa1a5f0136f88351303e9b5f59bc39cd7f399b1e6d0c4e2381e837"
)
EXPECTED_CORRECTED_TEST_GIT_BLOB = "6f907211ef870d582228bd1f4400bf90c757eb56"
EXPECTED_ACCEPTED_SHA256 = {
    V1_PACKET_REL: "41994b0c1703d7f7f7ff7aeda217900a3136489f070ae55a88f2db10a13d12c0",
    V1_REVIEW_REL: "4b99d6d3801a8bbd2f918311116dfdfce8ef595f7c0e1b629bc3595820612dca",
    V1_CONSUMER_REL: "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
    V1_CUSTODY_REL: "bc35c992c9b9fd7dd9c2e84ed6d5b89463b3ce8eb13dc2f7c7d1c539b4d23ce9",
    REGISTRY_REL: "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
    AUTHORITY_REL: "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
    MAINTENANCE_REL: "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
}
EXPECTED_ROOTS = {
    "authority_commitment_sha256": (
        "fd4348411236648d6216900eced59524b87c561bfa0d36186cf4c4d19a2e6b34"
    ),
    "full_record_identity_root_sha256": (
        "67a23fda6348a2a6e12e4c2af775d115c692ecbe4d0650f0844a982d869e112d"
    ),
    "identity_payload_pointer_root_sha256": (
        "a97799ea412006dde3c259b718b10aad9dee7012181611f3f1d5f1a1e821a967"
    ),
    "original_pointer_set_sha256": (
        "219f4bc866b731b74ef50a439b6a869d8add33c6c5ce8e83a621115c1649c6bf"
    ),
}

FORBIDDEN_PRODUCTION_PATHS = [
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


@lru_cache(maxsize=None)
def _git_blob(commit: str, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise IndependentReviewError(
            f"missing immutable review input {commit}:{relative}"
        )
    return result.stdout


def _git_blob_oid(commit: str, relative: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise IndependentReviewError(
            f"missing immutable review object {commit}:{relative}"
        )
    return result.stdout.strip()


def _git_path_absent(commit: str, relative: str) -> bool:
    result = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", commit, "--", relative],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return not result.stdout.strip()


def _reject_constant(value: str) -> Any:
    raise IndependentReviewError(f"non-finite JSON constant rejected: {value}")


def _unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise IndependentReviewError(f"duplicate JSON key rejected: {key}")
        output[key] = value
    return output


def _strict_json_value(raw: bytes) -> Any:
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise IndependentReviewError("invalid UTF-8 rejected") from exc
    if text.startswith("\ufeff"):
        raise IndependentReviewError("UTF-8 BOM rejected")
    try:
        return json.loads(
            text,
            object_pairs_hook=_unique_pairs,
            parse_constant=_reject_constant,
        )
    except json.JSONDecodeError as exc:
        raise IndependentReviewError("invalid JSON rejected") from exc


def _strict_canonical_artifact(raw: bytes) -> dict[str, Any]:
    if b"\r" in raw:
        raise IndependentReviewError("CR or CRLF rejected")
    if not raw.endswith(b"\n") or raw.endswith(b"\n\n"):
        raise IndependentReviewError("exactly one terminal LF required")
    payload = _strict_json_value(raw)
    if not isinstance(payload, dict):
        raise IndependentReviewError("reviewed artifact root must be an object")
    if canonical_json_bytes(payload) != raw:
        raise IndependentReviewError("reviewed artifact is not canonical JSON")
    return payload


def _strict_parser_probe_count() -> int:
    invalid = [
        b'{"a":1,"a":2}\n',
        b'{"a":NaN}\n',
        b'{"a":Infinity}\n',
        b'\xef\xbb\xbf{"a":1}\n',
        b'{"a":1}\r\n',
        b'{"a":1}\n\n',
    ]
    for raw in invalid:
        try:
            _strict_canonical_artifact(raw)
        except IndependentReviewError:
            continue
        raise IndependentReviewError(f"strict parser probe falsely accepted: {raw!r}")
    valid = canonical_json_bytes({"a": 1, "b": [True, None]})
    if _strict_canonical_artifact(valid) != {"a": 1, "b": [True, None]}:
        raise IndependentReviewError("strict parser positive probe failed")
    return len(invalid) + 1


def _verify_input_hashes() -> None:
    for path, expected in EXPECTED_PREPARATION_SHA256.items():
        if _sha256(_git_blob(PREPARATION_COMMIT, path)) != expected:
            raise IndependentReviewError(f"preparation SHA-256 drift: {path}")
    for path, expected in EXPECTED_PREPARATION_GIT_BLOBS.items():
        if _git_blob_oid(PREPARATION_COMMIT, path) != expected:
            raise IndependentReviewError(f"preparation Git blob drift: {path}")
    for path, expected in EXPECTED_ACCEPTED_SHA256.items():
        if _sha256(_git_blob(ACCEPTED_SOURCE_COMMIT, path)) != expected:
            raise IndependentReviewError(f"accepted-source SHA-256 drift: {path}")
    corrected_test = _git_blob(CORRECTED_REVIEW_BOUNDARY_COMMIT, PREPARATION_TEST_REL)
    if _sha256(corrected_test) != EXPECTED_CORRECTED_TEST_SHA256:
        raise IndependentReviewError("corrected preparation-test SHA-256 drift")
    if (
        _git_blob_oid(CORRECTED_REVIEW_BOUNDARY_COMMIT, PREPARATION_TEST_REL)
        != EXPECTED_CORRECTED_TEST_GIT_BLOB
    ):
        raise IndependentReviewError("corrected preparation-test Git blob drift")

    changed = subprocess.run(
        [
            "git",
            "diff",
            "--name-only",
            PREPARATION_COMMIT,
            CORRECTED_REVIEW_BOUNDARY_COMMIT,
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    if changed != [PREPARATION_TEST_REL]:
        raise IndependentReviewError("portability correction changed unexpected paths")
    original_test = _git_blob(PREPARATION_COMMIT, PREPARATION_TEST_REL)
    expected_corrected_test = original_test.replace(
        b"import subprocess\n", b"import subprocess\nimport sys\n", 1
    ).replace(
        b'str(readiness.REPO_ROOT / ".venv/Scripts/python.exe"),',
        b"sys.executable,",
        1,
    )
    if corrected_test != expected_corrected_test:
        raise IndependentReviewError(
            "portability correction is not the exact sys.executable repair"
        )
    for path in (
        PACKET_REL,
        SCHEMA_REL,
        PROTOCOL_REL,
        PREPARATION_GENERATOR_REL,
        PREPARATION_LEAN_REL,
    ):
        if _git_blob_oid(CORRECTED_REVIEW_BOUNDARY_COMMIT, path) != (
            EXPECTED_PREPARATION_GIT_BLOBS[path]
        ):
            raise IndependentReviewError(
                f"portability correction altered immutable preparation input: {path}"
            )


def _schema_review(bundle: dict[str, Any]) -> dict[str, Any]:
    expected_names = {
        "compatibility_reconstruction_result",
        "consumer_source_map",
        "control_harness_report",
        "current_projection",
        "history_index",
        "history_shard_record",
        "legacy_byte_custody_manifest",
        "runtime_shadow_trace_event",
        "runtime_shadow_trace_manifest",
        "validation_report",
    }
    schemas = bundle.get("schemas")
    if not isinstance(schemas, dict) or set(schemas) != expected_names:
        raise IndependentReviewError("closed-schema set mismatch")
    if bundle.get("schema_count") != 10 or bundle.get("draft") != "JSON_SCHEMA_2020_12":
        raise IndependentReviewError("closed-schema count or draft mismatch")

    object_schema_count = 0
    empty_schema_slot_count = 0
    closure_error_count = 0

    def visit(node: Any) -> None:
        nonlocal object_schema_count, empty_schema_slot_count, closure_error_count
        if isinstance(node, dict):
            if not node:
                empty_schema_slot_count += 1
            has_properties = "properties" in node
            type_value = node.get("type")
            is_object = type_value == "object" or (
                isinstance(type_value, list) and "object" in type_value
            )
            if has_properties or is_object:
                object_schema_count += 1
                properties = node.get("properties")
                required = node.get("required")
                if (
                    type_value != "object"
                    or not isinstance(properties, dict)
                    or node.get("additionalProperties") is not False
                    or not isinstance(required, list)
                    or set(required) != set(properties)
                ):
                    closure_error_count += 1
            if node.get("additionalProperties") not in (None, False):
                closure_error_count += 1
            for value in node.values():
                visit(value)
        elif isinstance(node, list):
            for value in node:
                visit(value)

    for schema in schemas.values():
        if schema.get("$schema") != "https://json-schema.org/draft/2020-12/schema":
            raise IndependentReviewError("schema dialect mismatch")
        Draft202012Validator.check_schema(schema)
        visit(schema)

    if object_schema_count != 47:
        raise IndependentReviewError("unexpected recursively closed object-schema count")
    if empty_schema_slot_count or closure_error_count:
        raise IndependentReviewError("unconstrained or non-closed schema slot detected")

    canonical = bundle.get("canonical_instance_bytes")
    expected_canonical = {
        "allow_nan": False,
        "duplicate_keys_rejected_before_schema_evaluation": True,
        "encoding": "UTF-8_NO_BOM",
        "final_newline": "EXACTLY_ONE_LF",
        "key_order": "LEXICOGRAPHIC",
        "line_endings": "LF_ONLY",
        "unknown_fields_rejected": True,
    }
    if canonical != expected_canonical:
        raise IndependentReviewError("strict parser/canonical-byte boundary drift")
    return {
        "draft": "2020-12",
        "empty_or_unconstrained_slot_count": empty_schema_slot_count,
        "metaschema_validation_passed": True,
        "object_schema_count": object_schema_count,
        "recursive_closure_error_count": closure_error_count,
        "schema_count": len(schemas),
        "strict_parser_contract_present": True,
    }


def _json_pointer_token(value: str) -> str:
    return value.replace("~", "~0").replace("/", "~1")


def _independent_record_review() -> dict[str, Any]:
    registry_raw = _git_blob(ACCEPTED_SOURCE_COMMIT, REGISTRY_REL)
    if len(registry_raw) != 52_340_650:
        raise IndependentReviewError("source registry byte-size drift")
    registry = _strict_json_value(registry_raw)
    if not isinstance(registry, dict):
        raise IndependentReviewError("legacy registry is not an object")
    workstreams = registry.get("workstreams")
    if not isinstance(workstreams, list):
        raise IndependentReviewError("legacy workstreams is not a list")
    root_keys = [key for key in registry if key != "workstreams"]
    records: list[tuple[str, str, str, Any]] = []
    for key in root_keys:
        records.append(("ROOT_FIELD", key, f"/{_json_pointer_token(key)}", registry[key]))
    for index, row in enumerate(workstreams):
        if not isinstance(row, dict):
            raise IndependentReviewError("legacy workstream is not an object")
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
    for record_class, logical_key, pointer, payload in records:
        payload_sha = _sha256(compact_json_bytes(payload))
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
                "source_git_blob": "e6c5b3773dccd92fde9c0a8d486a56f993d6b235",
                "source_path": REGISTRY_REL,
            }
        )
        record_id = "lcr1:" + _sha256(preimage)
        record_ids.append(record_id)
        identity_rows.append(f"{record_id}:{payload_sha}:{pointer}")
        pointers.append(pointer)

    maintenance = _strict_json_value(
        _git_blob(ACCEPTED_SOURCE_COMMIT, MAINTENANCE_REL)
    )
    authority_payload = {
        "active_workstream_sha256": _sha256(
            compact_json_bytes(registry.get("active_workstreams", [None])[0])
        ),
        "legacy_current_projection": registry.get("current_projection_v0"),
        "maintenance_authority": maintenance,
    }
    roots = {
        "authority_commitment_sha256": _sha256(compact_json_bytes(authority_payload)),
        "full_record_identity_root_sha256": _sha256(
            "\n".join(sorted(record_ids)).encode("utf-8")
        ),
        "identity_payload_pointer_root_sha256": _sha256(
            "\n".join(sorted(identity_rows)).encode("utf-8")
        ),
        "original_pointer_set_sha256": _sha256(
            "\n".join(sorted(pointers)).encode("utf-8")
        ),
    }
    if roots != EXPECTED_ROOTS:
        raise IndependentReviewError("independently reproduced v1 roots mismatch")
    if len(root_keys) != 4_152 or len(workstreams) != 539 or len(records) != 4_691:
        raise IndependentReviewError("independent record accounting mismatch")
    if len(record_ids) != len(set(record_ids)):
        raise IndependentReviewError("independent record identity collision")
    current_projection = registry.get("current_projection_v0")
    if not isinstance(current_projection, dict):
        raise IndependentReviewError("legacy current projection missing")
    if current_projection.get("current_target") != SCIENTIFIC_TARGET:
        raise IndependentReviewError("scientific target drift")
    if maintenance.get("current_maintenance_target") != MAINTENANCE_TARGET:
        raise IndependentReviewError("maintenance target drift")
    if maintenance.get("scientific_authority", {}).get("current_target") != SCIENTIFIC_TARGET:
        raise IndependentReviewError("maintenance scientific mirror drift")
    return {
        **roots,
        "record_id_collision_count": 0,
        "root_field_record_count": len(root_keys),
        "source_registry_sha256": _sha256(registry_raw),
        "source_registry_size_bytes": len(registry_raw),
        "targets_reproduced_from_legacy_and_maintenance_authority": True,
        "total_record_count": len(records),
        "workstream_record_count": len(workstreams),
    }


def _control_review(
    protocol: dict[str, Any], v1_packet: dict[str, Any]
) -> dict[str, Any]:
    harness = protocol.get("typed_control_harness")
    if not isinstance(harness, dict):
        raise IndependentReviewError("typed control harness missing")
    controls = harness.get("controls")
    v1_controls = v1_packet.get("negative_controls")
    if not isinstance(controls, list) or not isinstance(v1_controls, list):
        raise IndependentReviewError("control lists missing")
    if len(controls) != 52 or len(v1_controls) != 52:
        raise IndependentReviewError("control count mismatch")
    for index, (control, v1_control) in enumerate(zip(controls, v1_controls), start=1):
        expected_id = f"REGISTRY-V1-NC-{index:03d}"
        if control.get("control_id") != expected_id:
            raise IndependentReviewError("control ordering or identity mismatch")
        if control.get("mutation") != v1_control.get("mutation"):
            raise IndependentReviewError(f"control mutation mismatch: {expected_id}")
        if control.get("expected_exact_error_set") != [
            v1_control.get("expected_error_code")
        ]:
            raise IndependentReviewError(f"control error code mismatch: {expected_id}")
        if control.get("v0_false_acceptance_regression") != v1_control.get(
            "v0_false_acceptance_regression"
        ):
            raise IndependentReviewError(f"control regression flag mismatch: {expected_id}")
        if control.get("execution_status") != "NOT_EXECUTED_PREPARATION_ONLY":
            raise IndependentReviewError(f"control falsely reports execution: {expected_id}")
        if control.get("expected_decision") != "REJECT":
            raise IndependentReviewError(f"control decision mismatch: {expected_id}")
        if not control.get("baseline_candidate_recreated_before_mutation"):
            raise IndependentReviewError(f"control isolation missing: {expected_id}")
        if not control.get("subsequent_controls_receive_unmodified_baseline"):
            raise IndependentReviewError(f"control baseline custody missing: {expected_id}")

    profiles = harness.get("validator_profiles")
    if not isinstance(profiles, dict) or set(profiles) != {
        "PROTOTYPE_INTEGRITY",
        "WRITE_SAFETY",
        "SHADOW_PARITY",
        "CUTOVER_ELIGIBILITY",
    }:
        raise IndependentReviewError("validator profile set mismatch")
    profile_counts = Counter(row["validator_profile"] for row in controls)
    if profile_counts != Counter(
        {
            "PROTOTYPE_INTEGRITY": 47,
            "WRITE_SAFETY": 2,
            "SHADOW_PARITY": 2,
            "CUTOVER_ELIGIBILITY": 1,
        }
    ):
        raise IndependentReviewError("validator profile distribution mismatch")
    by_id = {row["control_id"]: row for row in controls}
    expected_special = {
        "REGISTRY-V1-NC-041": "WRITE_SAFETY",
        "REGISTRY-V1-NC-042": "WRITE_SAFETY",
        "REGISTRY-V1-NC-044": "CUTOVER_ELIGIBILITY",
        "REGISTRY-V1-NC-045": "SHADOW_PARITY",
        "REGISTRY-V1-NC-046": "SHADOW_PARITY",
    }
    if {key: by_id[key]["validator_profile"] for key in expected_special} != expected_special:
        raise IndependentReviewError("special validator-profile assignment mismatch")
    baselines = [row.get("positive_baseline") for row in profiles.values()]
    if None in baselines or len(baselines) != len(set(baselines)):
        raise IndependentReviewError("validator profiles lack distinct positive baselines")
    interface = protocol.get("production_validator_interface", {})
    functions = interface.get("profile_specific_entrypoints", [])
    if len(functions) != 4 or len(set(functions)) != 4:
        raise IndependentReviewError("profile-specific validator entrypoints missing")
    if any(re.search(r"\bmode\b", function, re.IGNORECASE) for function in functions):
        raise IndependentReviewError("candidate-selectable validator mode detected")
    if interface.get("profile_selected_by_caller_not_candidate") is not True:
        raise IndependentReviewError("caller-selected validator profile not frozen")
    if harness.get("profile_is_caller_selected_never_candidate_selected") is not True:
        raise IndependentReviewError("harness permits candidate-selected profile")
    if harness.get("production_validator_exists") is not False:
        raise IndependentReviewError("preparation falsely claims a production validator")
    if harness.get("execution_complete") is not False:
        raise IndependentReviewError("preparation falsely claims control execution")
    return {
        "candidate_selected_mode_present": False,
        "control_count": len(controls),
        "controls_executed": False,
        "distinct_positive_baseline_count": len(set(baselines)),
        "exact_v1_control_identity_and_error_mapping": True,
        "profile_counts": dict(sorted(profile_counts.items())),
        "special_profile_assignments": expected_special,
        "v0_false_acceptance_regression_count": sum(
            bool(row["v0_false_acceptance_regression"]) for row in controls
        ),
    }


def _consumer_review(
    protocol: dict[str, Any], schema_bundle: dict[str, Any]
) -> dict[str, Any]:
    consumer = _strict_canonical_artifact(
        _git_blob(ACCEPTED_SOURCE_COMMIT, V1_CONSUMER_REL)
    )
    if consumer.get("consumer_count") != 496:
        raise IndependentReviewError("static consumer baseline count mismatch")
    shadow = protocol.get("runtime_shadow_tracing_protocol", {})
    required = {
        "all_496_static_rows_require_final_disposition": True,
        "baseline_count_is_not_an_eternal_current_count": True,
        "fresh_full_tree_rescan_and_structured_delta_required": True,
        "unobserved_required_consumer_waiver_allowed": False,
        "consumer_migration_or_cutover_during_trace": False,
    }
    for key, expected in required.items():
        if shadow.get(key) is not expected:
            raise IndependentReviewError(f"shadow consumer boundary mismatch: {key}")
    schema = schema_bundle["schemas"]["consumer_source_map"]
    baseline_schema = schema["properties"]["baseline"]["properties"]
    if baseline_schema["consumer_count"].get("const") != 496:
        raise IndependentReviewError("consumer schema does not bind 496 baseline")
    current_scan = schema["properties"]["current_scan"]
    if set(current_scan["required"]) != {
        "added_consumer_ids",
        "changed_consumer_ids",
        "consumer_count",
        "removed_consumer_ids",
        "source_commit",
        "unclassified_count",
    }:
        raise IndependentReviewError("fresh consumer scan/delta schema incomplete")
    if current_scan["properties"]["unclassified_count"].get("const") != 0:
        raise IndependentReviewError("consumer schema permits unclassified rows")
    return {
        "baseline_consumer_count": 496,
        "baseline_source_map_sha256": EXPECTED_ACCEPTED_SHA256[V1_CONSUMER_REL],
        "baseline_treated_as_eternal_current_count": False,
        "consumer_migration_or_cutover_authorized_during_trace": False,
        "fresh_full_tree_rescan_required": True,
        "structured_added_removed_changed_delta_required": True,
        "unclassified_current_consumer_count_allowed": 0,
    }


def _custody_review(
    protocol: dict[str, Any], schema_bundle: dict[str, Any]
) -> dict[str, Any]:
    custody = protocol.get("byte_custody_execution_procedure", {})
    acceptance = custody.get("acceptance")
    expected_acceptance = {
        "byte_identical": True,
        "decompressed_sha256": EXPECTED_ACCEPTED_SHA256[REGISTRY_REL],
        "decompressed_size_bytes": 52_340_650,
        "detached_clean_checkout_required": True,
        "reconstructed_sha256": EXPECTED_ACCEPTED_SHA256[REGISTRY_REL],
    }
    if acceptance != expected_acceptance:
        raise IndependentReviewError("byte-custody execution acceptance drift")
    if custody.get("semantic_equivalence_alone_sufficient") is not False:
        raise IndependentReviewError("semantic-only custody incorrectly accepted")
    schema = schema_bundle["schemas"]["legacy_byte_custody_manifest"]
    reconstruction = schema["properties"]["reconstruction_requirement"]["properties"]
    if reconstruction["byte_identical"].get("const") is not True:
        raise IndependentReviewError("custody manifest does not require byte identity")
    if reconstruction["decompressed_sha256"].get("const") != EXPECTED_ACCEPTED_SHA256[REGISTRY_REL]:
        raise IndependentReviewError("custody manifest source hash mismatch")
    if reconstruction["decompressed_size_bytes"].get("const") != 52_340_650:
        raise IndependentReviewError("custody manifest source size mismatch")
    gzip_profile = schema["properties"]["gzip_profile"]["properties"]
    expected_gzip = {
        "cm": 8,
        "compression_level": 9,
        "flg": 0,
        "member_count": 1,
        "mtime": 0,
        "os": 255,
        "trailing_byte_count": 0,
        "xfl": 2,
    }
    for key, expected in expected_gzip.items():
        if gzip_profile[key].get("const") != expected:
            raise IndependentReviewError(f"gzip profile drift: {key}")
    return {
        "custody_payload_created": False,
        "detached_clean_checkout_required": True,
        "gzip_profile_closed_and_single_member": True,
        "legacy_byte_identity_required": True,
        "semantic_equivalence_alone_sufficient": False,
        "source_registry_sha256": EXPECTED_ACCEPTED_SHA256[REGISTRY_REL],
        "source_registry_size_bytes": 52_340_650,
    }


def _adversarial_contract_review(
    protocol: dict[str, Any], schema_bundle: dict[str, Any]
) -> dict[str, Any]:
    schemas = schema_bundle["schemas"]

    validation_schema = schemas["validation_report"]
    path_schema = validation_schema["properties"]["issues"]["items"][
        "properties"
    ]["artifact_path"]
    false_accepted_paths = [
        path
        for path in ["/absolute/path.json", "//server/share/registry.json"]
        if Draft202012Validator(path_schema).is_valid(path)
    ]
    if false_accepted_paths != [
        "/absolute/path.json",
        "//server/share/registry.json",
    ]:
        raise IndependentReviewError("expected path-schema false acceptance changed")

    history_false_candidate = {
        "identical_occurrence_ordinal": 0,
        "logical_key": "false_acceptance",
        "original_json_pointer": "/false_acceptance",
        "payload_canonical_json_utf8_base64": "!!!!",
        "payload_kind": "OBJECT",
        "payload_sha256": "0" * 64,
        "payload_size_bytes": 999,
        "record_class": "ROOT_FIELD",
        "record_id": "lcr1:" + "1" * 64,
        "record_version": 1,
        "schema_id": "LOOP_CONTROL_HISTORY_RECORD_v1",
        "source_git_blob": "e6c5b3773dccd92fde9c0a8d486a56f993d6b235",
        "source_path": REGISTRY_REL,
    }
    history_false_acceptance = Draft202012Validator(
        schemas["history_shard_record"]
    ).is_valid(history_false_candidate)
    if not history_false_acceptance:
        raise IndependentReviewError("expected history-payload false acceptance changed")

    validation_false_candidate = {
        "candidate_root_sha256": "2" * 64,
        "issues": [
            {
                "artifact_path": "relative/artifact.json",
                "control_id": None,
                "error_code": "V1-E-SCHEMA",
                "json_pointer": "/",
                "message": "an issue exists",
            }
        ],
        "passed": True,
        "profile": "PROTOTYPE_INTEGRITY",
        "schema_id": "LOOP_CONTROL_VALIDATION_REPORT_v1",
        "trust_anchor_sha256": "3" * 64,
    }
    validation_report_false_acceptance = Draft202012Validator(
        validation_schema
    ).is_valid(validation_false_candidate)
    if not validation_report_false_acceptance:
        raise IndependentReviewError("expected validation-report false acceptance changed")

    harness_false_candidate = {
        "base_candidate_sha256_after": "4" * 64,
        "base_candidate_sha256_before": "5" * 64,
        "control_count": 52,
        "controls_passed": 52,
        "profile_reports": [
            {
                "baseline_after_passed": True,
                "baseline_before_passed": True,
                "control_count": count,
                "controls_passed": count,
                "profile": "PROTOTYPE_INTEGRITY",
            }
            for count in range(1, 5)
        ],
        "schema_id": "LOOP_CONTROL_CONTROL_HARNESS_REPORT_v1",
        "status": "ALL_ISOLATED_CONTROLS_PASSED",
    }
    harness_report_false_acceptance = Draft202012Validator(
        schemas["control_harness_report"]
    ).is_valid(harness_false_candidate)
    if not harness_report_false_acceptance:
        raise IndependentReviewError("expected harness-report false acceptance changed")

    profiles = protocol["typed_control_harness"]["validator_profiles"]
    cutover = profiles["CUTOVER_ELIGIBILITY"]
    shadow = profiles["SHADOW_PARITY"]
    profile_requirement_conflict = (
        cutover.get("extends") == "SHADOW_PARITY"
        and shadow.get("legacy_monolith_readers_required") is True
        and cutover.get("legacy_monolith_readers_required") is False
    )
    if not profile_requirement_conflict:
        raise IndependentReviewError("expected cutover/shadow requirement conflict changed")
    if "inheritance_override_semantics" in protocol["typed_control_harness"]:
        raise IndependentReviewError("unexpected profile override semantics now present")

    return {
        "cutover_shadow_reader_requirement_conflict": profile_requirement_conflict,
        "history_payload_cross_field_false_acceptance": history_false_acceptance,
        "history_payload_required_runtime_checks_absent": [
            "STRICT_BASE64_DECODE",
            "DECODED_SIZE_EQUALS_PAYLOAD_SIZE_BYTES",
            "DECODED_SHA256_EQUALS_PAYLOAD_SHA256",
            "DECODED_KIND_EQUALS_PAYLOAD_KIND",
            "RECOMPUTED_RECORD_ID_EQUALS_RECORD_ID",
        ],
        "harness_report_cross_field_false_acceptance": harness_report_false_acceptance,
        "path_false_acceptances": false_accepted_paths,
        "validation_report_cross_field_false_acceptance": (
            validation_report_false_acceptance
        ),
    }


def _nonauthorization_review(
    packet: dict[str, Any], protocol: dict[str, Any]
) -> dict[str, Any]:
    groups: dict[str, list[bool]] = {
        "accepted_v1": [
            packet["accepted_v1_input"]["migration_execution_readiness_accepted"]
        ],
        "packet_authorization": [
            value
            for value in packet["authorization"].values()
            if isinstance(value, bool)
        ],
        "packet_boundary": list(packet["boundary"].values()),
        "readiness_levels": [
            value["currently_satisfied"]
            for value in packet["readiness_levels"].values()
        ],
        "protocol_authorization": list(protocol["authorization"].values()),
        "harness_execution": [
            protocol["typed_control_harness"]["production_validator_exists"],
            protocol["typed_control_harness"]["execution_complete"],
        ],
    }
    if not all(value is False for values in groups.values() for value in values):
        raise IndependentReviewError("nonauthorization boolean unexpectedly true")
    if packet["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewError("packet scientific target mismatch")
    if packet["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewError("packet maintenance target mismatch")
    return {
        "all_false": True,
        "group_counts": {key: len(values) for key, values in groups.items()},
        "nonauthorization_boolean_count": sum(len(values) for values in groups.values()),
    }


@lru_cache(maxsize=1)
def build_review() -> dict[str, Any]:
    _verify_input_hashes()
    packet = _strict_canonical_artifact(_git_blob(PREPARATION_COMMIT, PACKET_REL))
    schema_bundle = _strict_canonical_artifact(
        _git_blob(PREPARATION_COMMIT, SCHEMA_REL)
    )
    protocol = _strict_canonical_artifact(
        _git_blob(PREPARATION_COMMIT, PROTOCOL_REL)
    )
    v1_packet = _strict_canonical_artifact(
        _git_blob(ACCEPTED_SOURCE_COMMIT, V1_PACKET_REL)
    )
    v1_review = _strict_canonical_artifact(
        _git_blob(ACCEPTED_SOURCE_COMMIT, V1_REVIEW_REL)
    )

    schema_review = _schema_review(schema_bundle)
    parser_probe_count = _strict_parser_probe_count()
    record_review = _independent_record_review()
    control_review = _control_review(protocol, v1_packet)
    consumer_review = _consumer_review(protocol, schema_bundle)
    custody_review = _custody_review(protocol, schema_bundle)
    adversarial_review = _adversarial_contract_review(protocol, schema_bundle)
    nonauthorization_review = _nonauthorization_review(packet, protocol)

    if v1_review["accepted_scope"]["migration_execution_readiness"] is not False:
        raise IndependentReviewError("accepted v1 review boundary drift")
    if packet["packet_target"] != PACKET_TARGET:
        raise IndependentReviewError("readiness packet target drift")
    if packet["status"] != (
        "EXECUTION_READINESS_PREPARATION_CONTRACT_FROZEN_REVIEW_REQUIRED_"
        "NO_PROTOTYPE_MIGRATION_CUTOVER_OR_AUTHORITY"
    ):
        raise IndependentReviewError("readiness packet status drift")
    if any(
        not _git_path_absent(CORRECTED_REVIEW_BOUNDARY_COMMIT, path)
        for path in FORBIDDEN_PRODUCTION_PATHS
    ):
        raise IndependentReviewError("production or prototype artifact exists at review commit")

    lock = protocol.get("validator_engine_and_lock_contract", {})
    requirements_ci = _git_blob(ACCEPTED_SOURCE_COMMIT, "requirements.ci.lock").decode(
        "utf-8"
    )
    requirements_active = _git_blob(
        ACCEPTED_SOURCE_COMMIT, "requirements.active.lock"
    ).decode("utf-8")
    direct_pattern = re.compile(r"(?mi)^jsonschema(?:\[[^]]+\])?==")
    direct_ci = bool(direct_pattern.search(requirements_ci))
    direct_active = bool(direct_pattern.search(requirements_active))
    observed_jsonschema = version("jsonschema")
    if observed_jsonschema != "4.26.0":
        raise IndependentReviewError("review runtime jsonschema version drift")
    if direct_ci or direct_active:
        raise IndependentReviewError("direct jsonschema lock unexpectedly present")
    if lock != {
        "direct_requirements_lock_entry_present_at_source_commit": False,
        "duplicate_key_and_nonfinite_checks_are_parser_level_not_schema_only": True,
        "engine": "jsonschema",
        "implementation_blocked_until_direct_lock_and_transitive_closure_reviewed": True,
        "required_draft": "2020-12",
        "required_exact_version": "4.26.0",
        "requirements_path": "requirements.ci.lock",
    }:
        raise IndependentReviewError("validator engine blocker contract drift")

    return {
        "accepted_scope": {
            "closed_schema_preparation_contract": False,
            "execution_protocol_preparation_contract": False,
            "historical_preparation_evidence": True,
            "packet_acceptance": False,
            "prototype_selection": False,
            "registry_cutover": False,
            "registry_migration_execution_readiness": False,
        },
        "adversarial_contract_review": adversarial_review,
        "authorization": {
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_rotation_authorized": False,
            "prototype_execution_target_selected": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_rotation_authorized": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "consumer_review": consumer_review,
        "control_harness_review": control_review,
        "custody_review": custody_review,
        "findings": [
            {
                "finding_id": "REGISTRY-READINESS-REVIEW-001",
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "CUTOVER_ELIGIBILITY extends SHADOW_PARITY, whose positive baseline "
                    "requires legacy monolith readers, while the cutover profile requires "
                    "those readers to be absent; no inheritance override or requirement "
                    "resolution semantics are frozen."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-REVIEW-002",
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "The history-record schema treats contentEncoding as an annotation and "
                    "the protocol does not require strict base64 decoding or enforce decoded "
                    "payload size, hash, kind, canonical bytes, and recomputed record-ID "
                    "relations; an invalid mutually inconsistent record validates."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-REVIEW-003",
                "packet_defect": True,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_PACKET_ACCEPTANCE_AND_ALL_EXECUTION",
                "summary": (
                    "The reusable repository-path schema rejects drive-qualified and "
                    "backslash paths but accepts POSIX absolute paths and forward-slash "
                    "UNC-style paths such as //server/share."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-REVIEW-004",
                "packet_defect": True,
                "severity": "MEDIUM",
                "status": "OPEN_REQUIRES_VERSIONED_SCHEMA_CORRECTION",
                "summary": (
                    "Report schemas do not enforce decision invariants: a validation report "
                    "can declare passed=true with nonempty issues, and a harness report can "
                    "declare 52/52 while omitting distinct profiles, mismatching profile sums, "
                    "or changing the base candidate hash."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-REVIEW-005",
                "packet_defect": False,
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_READ_ONLY_PROTOTYPE_SELECTION_NOT_PACKET_ACCEPTANCE",
                "summary": (
                    "jsonschema 4.26.0 is available to this review but is not a direct "
                    "dependency in either committed requirements lock; the packet correctly "
                    "keeps implementation and prototype selection blocked until the engine "
                    "and transitive closure are directly locked and reviewed."
                ),
            }
        ],
        "immutable_input_review": {
            "accepted_source_commit": ACCEPTED_SOURCE_COMMIT,
            "corrected_review_boundary_commit": CORRECTED_REVIEW_BOUNDARY_COMMIT,
            "original_preparation_commit": PREPARATION_COMMIT,
            "portability_correction": {
                "changed_path_count": 1,
                "corrected_test_git_blob": EXPECTED_CORRECTED_TEST_GIT_BLOB,
                "corrected_test_sha256": EXPECTED_CORRECTED_TEST_SHA256,
                "only_changed_path": PREPARATION_TEST_REL,
                "repair": "HARDCODED_WORKSPACE_VENV_INTERPRETER_REPLACED_BY_SYS_EXECUTABLE",
            },
            "preparation_git_blobs": dict(sorted(EXPECTED_PREPARATION_GIT_BLOBS.items())),
            "preparation_sha256": dict(sorted(EXPECTED_PREPARATION_SHA256.items())),
            "reviewed_via_git_show_only": True,
        },
        "nonauthorization_review": nonauthorization_review,
        "open_execution_obligations": [
            "PREPARE_AND_INDEPENDENTLY_REVIEW_A_VERSIONED_CORRECTIVE_SUCCESSOR",
            "REMOVE_CUTOVER_SHADOW_PROFILE_REQUIREMENT_AMBIGUITY",
            "FREEZE_AND_ENFORCE_HISTORY_PAYLOAD_CROSS_FIELD_VALIDATION",
            "REJECT_ALL_ABSOLUTE_AND_UNC_REPOSITORY_PATHS",
            "ENFORCE_VALIDATION_AND_CONTROL_REPORT_DECISION_INVARIANTS",
            "DIRECTLY_LOCK_VALIDATOR_ENGINE_AND_REVIEW_TRANSITIVE_CLOSURE",
            "IMPLEMENT_AND_VALIDATE_CLOSED_SCHEMAS_AND_STRICT_PARSER",
            "EXECUTE_ALL_52_CONTROLS_AGAINST_REAL_PROTOTYPE_CANDIDATES",
            "EXECUTE_FRESH_CONSUMER_RESCAN_AND_RUNTIME_SHADOW_PARITY",
            "EXECUTE_BYTE_EXACT_CUSTODY_AND_COMPATIBILITY_RECONSTRUCTION",
            "INDEPENDENTLY_REVIEW_READ_ONLY_PROTOTYPE_BEFORE_ANY_MIGRATION_SELECTION",
        ],
        "packet_sha256": EXPECTED_PREPARATION_SHA256[PACKET_REL],
        "path_absence_review": {
            "forbidden_path_count": len(FORBIDDEN_PRODUCTION_PATHS),
            "production_and_prototype_paths_absent": True,
        },
        "record_and_authority_review": record_review,
        "review_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v0"
        ),
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v0"
        ),
        "schema_review": schema_review,
        "status": (
            "REJECTED_EXECUTION_READINESS_PREPARATION_CONTRACT_V0_"
            "HISTORICAL_PREPARATION_EVIDENCE_ONLY_VERSIONED_CORRECTIVE_SUCCESSOR_REQUIRED_"
            "NO_PROTOTYPE_MIGRATION_OR_CUTOVER_AUTHORITY"
        ),
        "strict_parser_review": {
            "duplicate_key_and_nonfinite_rejection_is_parser_level": True,
            "production_strict_parser_present": False,
            "review_probe_count": parser_probe_count,
            "review_probes_passed": True,
        },
        "validator_engine_blocker": {
            "direct_requirements_active_lock_present": direct_active,
            "direct_requirements_ci_lock_present": direct_ci,
            "observed_review_runtime_version": observed_jsonschema,
            "packet_defect": False,
            "prototype_selection_blocked": True,
            "required_exact_version": "4.26.0",
        },
    }


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with open(handle, "wb", closefd=True) as stream:
            stream.write(raw)
            stream.flush()
        Path(temporary).replace(path)
    finally:
        candidate = Path(temporary)
        if candidate.exists():
            candidate.unlink()


def main() -> int:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true")
    group.add_argument("--write", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise SystemExit("independent review artifact is missing or stale")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
