from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "f9168ab5f566fb2019b9e76e68ff3e60e5c0dc52"
REGISTRY_PATH = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
PACKET_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v1.json"
)
CONSUMER_MAP_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
CUSTODY_CONTRACT_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_LEGACY_BYTE_CUSTODY_CONTRACT_20260711_v1.json"
)

REGISTRY_SIZE_BYTES = 52_340_650
REGISTRY_SHA256 = "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
REGISTRY_GIT_BLOB = "e6c5b3773dccd92fde9c0a8d486a56f993d6b235"
SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
TECHNICAL_DEBT_BASELINE_V1_SHA256 = (
    "a15b323953eb2e27de531dff9a094944ca398e80ddd1fe7bb04015c2889766ce"
)
REJECTED_V0_REVIEW_SHA256 = (
    "5e43181b11a4d302a301bd915a43a40636bf947d93edc9f327e9c0a7beceb485"
)
MAINTENANCE_AUTHORITY_SHA256 = (
    "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b"
)
CURRENT_AUTHORITATIVE_SURFACES_GIT_BLOB = (
    "d46c5fb1966dcefc6b923776b7d94c4f5009b889"
)
CURRENT_AUTHORITATIVE_SURFACES_SHA256 = (
    "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248"
)
FIXTURE_REPAIR_ACCEPTANCE_SHA256 = (
    "b1b0a6a68653e8f7e8e88eaf771be8ae1999f65131f3886d753031504a14a5f8"
)

V0_FALSE_ACCEPTANCES = [
    "authority_drift_with_rebound_fingerprint",
    "broken_current_index_pointer",
    "changed_history_with_rebound_index",
    "duplicate_shard_id",
    "nan_history_with_rebound_index",
    "noncanonical_jsonl",
    "oversized_current_projection",
    "two_maintenance_targets",
]

CONTROL_SPECS = [
    ("authority_drift_with_rebound_fingerprint", "V1-E-AUTHORITY-EXTERNAL-BINDING"),
    ("broken_current_index_pointer", "V1-E-INDEX-POINTER"),
    ("changed_history_with_rebound_index", "V1-E-HISTORY-EXTERNAL-ROOT"),
    ("duplicate_shard_id", "V1-E-SHARD-ID-DUPLICATE"),
    ("nan_history_with_rebound_index", "V1-E-JSON-NONFINITE"),
    ("noncanonical_jsonl", "V1-E-JSONL-NONCANONICAL"),
    ("oversized_current_projection", "V1-E-PROJECTION-SIZE"),
    ("two_maintenance_targets", "V1-E-MAINTENANCE-TARGET-CARDINALITY"),
    ("missing_projection_field", "V1-E-PROJECTION-FIELD-MISSING"),
    ("extra_projection_field", "V1-E-PROJECTION-FIELD-EXTRA"),
    ("history_record_in_projection", "V1-E-HISTORY-PROMOTED"),
    ("current_record_only_in_history", "V1-E-CURRENT-DEMOTED"),
    ("two_scientific_targets", "V1-E-SCIENTIFIC-TARGET-CARDINALITY"),
    ("claim_ceiling_drift", "V1-E-CLAIM-CEILING"),
    ("blocker_commitment_drift", "V1-E-BLOCKER-COMMITMENT"),
    ("nonpromotion_commitment_drift", "V1-E-NONPROMOTION-COMMITMENT"),
    ("missing_shard", "V1-E-SHARD-MISSING"),
    ("extra_shard", "V1-E-SHARD-EXTRA"),
    ("duplicate_shard_path", "V1-E-SHARD-PATH-DUPLICATE"),
    ("empty_shard", "V1-E-SHARD-EMPTY"),
    ("oversized_shard", "V1-E-SHARD-SIZE"),
    ("reordered_shards", "V1-E-SHARD-ORDER"),
    ("range_gap", "V1-E-SHARD-RANGE-GAP"),
    ("range_overlap", "V1-E-SHARD-RANGE-OVERLAP"),
    ("incorrect_shard_hash", "V1-E-SHARD-HASH"),
    ("incorrect_record_count", "V1-E-RECORD-COUNT"),
    ("duplicate_record_id", "V1-E-RECORD-ID-DUPLICATE"),
    ("forged_record_id", "V1-E-RECORD-ID-FORGED"),
    ("missing_record", "V1-E-RECORD-MISSING"),
    ("extra_record", "V1-E-RECORD-EXTRA"),
    ("duplicate_source_identity", "V1-E-SOURCE-IDENTITY-DUPLICATE"),
    ("ambiguous_record_id", "V1-E-RECORD-ID-AMBIGUOUS"),
    ("utf8_bom", "V1-E-UTF8-BOM"),
    ("invalid_utf8", "V1-E-UTF8-INVALID"),
    ("crlf_jsonl", "V1-E-JSONL-CRLF"),
    ("missing_terminal_newline", "V1-E-TERMINAL-NEWLINE"),
    ("blank_jsonl_line", "V1-E-JSONL-BLANK"),
    ("duplicate_json_key", "V1-E-JSON-KEY-DUPLICATE"),
    ("schema_version_drift", "V1-E-SCHEMA-VERSION"),
    ("path_traversal", "V1-E-PATH-TRAVERSAL"),
    ("closed_shard_write", "V1-E-CLOSED-SHARD-WRITE"),
    ("current_writer_touches_history", "V1-E-WRITE-SCOPE"),
    ("integrity_verification_bypass", "V1-E-VERIFY-BYPASS"),
    ("active_monolith_reader_remaining", "V1-E-MONOLITH-READER"),
    ("unclassified_consumer", "V1-E-CONSUMER-UNCLASSIFIED"),
    ("runtime_trace_incomplete", "V1-E-RUNTIME-COVERAGE"),
    ("gzip_multiple_members", "V1-E-CUSTODY-GZIP-MULTIMEMBER"),
    ("gzip_trailing_bytes", "V1-E-CUSTODY-GZIP-TRAILING"),
    ("gzip_header_drift", "V1-E-CUSTODY-GZIP-HEADER"),
    ("custody_decompressed_size_mismatch", "V1-E-CUSTODY-SIZE"),
    ("custody_decompressed_hash_mismatch", "V1-E-CUSTODY-HASH"),
    ("custody_history_semantic_root_disagreement", "V1-E-CUSTODY-SEMANTIC-ROOT"),
]

NONLITERAL_READERS = [
    "formal/python/tests/test_loop_control_registry_envelope_integrity_gate.py",
    "formal/python/tests/test_loop_control_registry_integrity_repair_custody_gate.py",
    "formal/python/tools/loop_control_registry_sharding_guardrail.py",
]

LANGUAGES = {
    ".py": "PYTHON",
    ".ps1": "POWERSHELL",
    ".yml": "YAML",
    ".yaml": "YAML",
    ".lean": "LEAN",
    ".md": "MARKDOWN",
    ".sh": "SHELL",
    ".toml": "TOML",
    ".json": "JSON",
    ".txt": "TEXT",
}


class GuardrailV1Error(ValueError):
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
def _git_blob(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise GuardrailV1Error(f"missing committed source blob: {relative}")
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


def _verify_source_registry() -> bytes:
    raw = _git_blob(REGISTRY_PATH)
    if len(raw) != REGISTRY_SIZE_BYTES:
        raise GuardrailV1Error("legacy registry byte-size drift")
    if _sha256(raw) != REGISTRY_SHA256:
        raise GuardrailV1Error("legacy registry SHA-256 drift")
    if _git_blob_oid(REGISTRY_PATH) != REGISTRY_GIT_BLOB:
        raise GuardrailV1Error("legacy registry Git blob drift")
    return raw


def _verify_external_inputs() -> None:
    checks = [
        (
            "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md",
            CURRENT_AUTHORITATIVE_SURFACES_SHA256,
            CURRENT_AUTHORITATIVE_SURFACES_GIT_BLOB,
        ),
        (
            "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json",
            MAINTENANCE_AUTHORITY_SHA256,
            None,
        ),
        (
            "formal/docs/release/TECHNICAL_DEBT_BASELINE_20260711_v1.json",
            TECHNICAL_DEBT_BASELINE_V1_SHA256,
            None,
        ),
        (
            "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_INDEPENDENT_REVIEW_20260711_v0.json",
            REJECTED_V0_REVIEW_SHA256,
            None,
        ),
        (
            "formal/docs/release/LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_ACCEPTANCE_20260711_v0.json",
            FIXTURE_REPAIR_ACCEPTANCE_SHA256,
            None,
        ),
        (
            "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json",
            "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
            "85711a7c8cb0bc6a1f77d85cf3873726a5d6aa22",
        ),
    ]
    for path, expected_sha, expected_blob in checks:
        if _sha256(_git_blob(path)) != expected_sha:
            raise GuardrailV1Error(f"external trust input SHA drift: {path}")
        if expected_blob is not None and _git_blob_oid(path) != expected_blob:
            raise GuardrailV1Error(f"external trust input Git blob drift: {path}")


def _json_pointer_token(value: str) -> str:
    return value.replace("~", "~0").replace("/", "~1")


@lru_cache(maxsize=1)
def record_commitments() -> dict[str, Any]:
    raw = _verify_source_registry()
    registry = json.loads(raw)
    root_keys = [key for key in registry if key != "workstreams"]
    workstreams = registry.get("workstreams")
    if not isinstance(workstreams, list):
        raise GuardrailV1Error("legacy workstreams is not a list")
    records: list[tuple[str, str, str, Any]] = []
    for key in root_keys:
        records.append(
            ("ROOT_FIELD", key, f"/{_json_pointer_token(key)}", registry[key])
        )
    for index, row in enumerate(workstreams):
        if not isinstance(row, dict):
            raise GuardrailV1Error("legacy workstream row is not an object")
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
    max_payload_bytes = 0
    for record_class, logical_key, pointer, payload in records:
        payload_raw = compact_json_bytes(payload)
        payload_sha = _sha256(payload_raw)
        max_payload_bytes = max(max_payload_bytes, len(payload_raw))
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
                "source_git_blob": REGISTRY_GIT_BLOB,
                "source_path": REGISTRY_PATH,
            }
        )
        record_id = "lcr1:" + _sha256(preimage)
        ids.append(record_id)
        identity_rows.append(f"{record_id}:{payload_sha}:{pointer}")
        pointers.append(pointer)

    if len(ids) != len(set(ids)):
        raise GuardrailV1Error("v1 record identity collision")
    if len(root_keys) != 4_152 or len(workstreams) != 539 or len(ids) != 4_691:
        raise GuardrailV1Error("legacy record accounting drift")

    active_workstream = registry.get("active_workstreams", [None])[0]
    authority_payload = {
        "active_workstream_sha256": _sha256(compact_json_bytes(active_workstream)),
        "legacy_current_projection": registry.get("current_projection_v0"),
        "maintenance_authority": json.loads(
            _git_blob("formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json")
        ),
    }
    return {
        "authority_commitment_sha256": _sha256(compact_json_bytes(authority_payload)),
        "full_record_identity_root_sha256": _sha256(
            "\n".join(sorted(ids)).encode("utf-8")
        ),
        "identity_payload_pointer_root_sha256": _sha256(
            "\n".join(sorted(identity_rows)).encode("utf-8")
        ),
        "maximum_canonical_payload_bytes": max_payload_bytes,
        "original_pointer_set_sha256": _sha256(
            "\n".join(sorted(pointers)).encode("utf-8")
        ),
        "root_field_record_count": len(root_keys),
        "total_record_count": len(ids),
        "workstream_record_count": len(workstreams),
    }


def _literal_references() -> dict[str, list[int]]:
    result = subprocess.run(
        [
            "git",
            "grep",
            "-n",
            "-F",
            "LOOP_CONTROL_REGISTRY_v0.json",
            SOURCE_COMMIT,
            "--",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    prefix = SOURCE_COMMIT + ":"
    matches: defaultdict[str, list[int]] = defaultdict(list)
    pattern = re.compile(r"^(.*?):(\d+):(.*)$")
    for raw_line in result.stdout.splitlines():
        line = raw_line[len(prefix) :] if raw_line.startswith(prefix) else raw_line
        parsed = pattern.match(line)
        if not parsed:
            raise GuardrailV1Error(f"unparsed git-grep result: {raw_line}")
        path, line_number, _ = parsed.groups()
        if path != REGISTRY_PATH:
            matches[path].append(int(line_number))
    return {path: sorted(set(lines)) for path, lines in matches.items()}


def _consumer_classification(path: str, raw: bytes, dynamic: bool) -> dict[str, Any]:
    suffix = Path(path).suffix.lower()
    text = raw.decode("utf-8", errors="replace")
    if dynamic:
        operation = "DYNAMIC_READER"
        confidence = "INDEPENDENT_REVIEW_IDENTIFIED_NONLITERAL_READER"
    elif path == "formal/python/tools/loop_control_registry_integrity.py":
        operation = "WRITER_AND_READER"
        confidence = "STATIC_LITERAL_AND_WRITE_ENTRYPOINT"
    elif suffix == ".py" and any(
        token in text for token in ("read_text", "read_bytes", "json.load", "open(")
    ):
        operation = "STATIC_READER_CANDIDATE"
        confidence = "LEXICAL_READER_EVIDENCE_RUNTIME_TRACE_PENDING"
    else:
        operation = "PATH_REFERENCE_ONLY"
        confidence = "LEXICAL_REFERENCE_NOT_RUNTIME_PROOF"

    if path.startswith("formal/python/tests/"):
        role = "TEST_ONLY_CONSUMER"
        batch = "CURRENT_AUTHORITY_AND_INTEGRITY_GATES"
    elif path.startswith("formal/python/tools/") or suffix in {".ps1", ".sh", ".yml", ".yaml"}:
        role = "ACTIVE_TOOL_OR_AUTOMATION"
        batch = "TOOLS_AUTOMATION_AND_WRITERS"
    elif suffix in {".md", ".txt"}:
        role = "DOCUMENTATION_ONLY_REFERENCE"
        batch = "DOCUMENTATION_REFERENCES"
    elif suffix == ".lean":
        role = "LEAN_CONSTANT_OR_CERTIFICATE_REFERENCE"
        batch = "LEAN_AND_GENERATED_CONSTANTS"
    else:
        role = "HISTORICAL_OR_STRUCTURED_REFERENCE"
        batch = "HISTORICAL_AND_STRUCTURED_REFERENCES"
    return {
        "access_operation": operation,
        "classification_confidence": confidence,
        "consumer_role": role,
        "migration_batch": batch,
        "runtime_trace_required": operation
        in {"DYNAMIC_READER", "WRITER_AND_READER", "STATIC_READER_CANDIDATE"},
        "schema_or_ordering_assumption": "UNRESOLVED_UNTIL_SHADOW_RUNTIME_TRACE"
        if operation != "PATH_REFERENCE_ONLY"
        else "NONE_PROVED_REFERENCE_ONLY",
    }


@lru_cache(maxsize=1)
def build_consumer_source_map() -> dict[str, Any]:
    literal = _literal_references()
    all_paths = sorted(set(literal) | set(NONLITERAL_READERS))
    rows = []
    for path in all_paths:
        raw = _git_blob(path)
        dynamic = path in NONLITERAL_READERS
        row = {
            "consumer_id": "lcc1:"
            + _sha256(
                compact_json_bytes(
                    {
                        "domain": "LOOP_CONTROL_CONSUMER_ID_v1",
                        "path": path,
                        "source_sha256": _sha256(raw),
                    }
                )
            ),
            "discovery_methods": (
                ["INDEPENDENT_NONLITERAL_SOURCE_ANALYSIS"]
                if dynamic
                else ["GIT_GREP_EXACT_LITERAL_AT_SOURCE_COMMIT"]
            ),
            "evidence_line_numbers": literal.get(path, []),
            "git_blob": _git_blob_oid(path),
            "language": LANGUAGES.get(Path(path).suffix.lower(), "OTHER"),
            "path": path,
            "source_sha256": _sha256(raw),
            "source_size_bytes": len(raw),
        }
        row.update(_consumer_classification(path, raw, dynamic))
        rows.append(row)

    if len(rows) != len({row["consumer_id"] for row in rows}):
        raise GuardrailV1Error("consumer identity collision")
    extension_counts = Counter(Path(path).suffix or "<none>" for path in literal)
    operation_counts = Counter(row["access_operation"] for row in rows)
    return {
        "boundary": {
            "consumer_migration_started": False,
            "runtime_coverage_complete": False,
            "static_inventory_claimed_as_runtime_complete": False,
        },
        "consumer_count": len(rows),
        "consumers": rows,
        "discovery": {
            "explicit_nonliteral_reader_count": len(NONLITERAL_READERS),
            "literal_extension_counts": dict(sorted(extension_counts.items())),
            "literal_external_path_count": len(literal),
            "operation_counts": dict(sorted(operation_counts.items())),
            "source_commit": SOURCE_COMMIT,
            "tracked_tree_scan": True,
        },
        "required_shadow_evidence": {
            "dynamic_path_construction_traced": False,
            "glob_readers_traced": False,
            "operation_class_parity_complete": False,
            "runtime_trace_complete": False,
            "writers_traced": False,
        },
        "schema_id": "LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1",
        "status": "STATIC_SOURCE_MAP_PREPARED_RUNTIME_COMPLETENESS_NOT_PROVED_NO_CONSUMER_MIGRATION",
    }


@lru_cache(maxsize=1)
def build_custody_contract() -> dict[str, Any]:
    raw = _verify_source_registry()
    transient = gzip.compress(raw, compresslevel=9, mtime=0)
    if gzip.decompress(transient) != raw:
        raise GuardrailV1Error("in-memory gzip round trip failed")
    return {
        "boundary": {
            "custody_payload_created": False,
            "legacy_monolith_modified_or_retired": False,
            "migration_execution_authorized": False,
        },
        "compatibility_reconstruction": {
            "acceptance": "BYTE_IDENTICAL_TO_FROZEN_LEGACY_SOURCE",
            "decompressed_sha256": REGISTRY_SHA256,
            "decompressed_size_bytes": REGISTRY_SIZE_BYTES,
            "semantic_reconstruction_alone_sufficient": False,
        },
        "container_contract": {
            "algorithm": "RFC1952_GZIP_SINGLE_MEMBER_DEFLATE",
            "compressed_container_hash_is_normative_before_execution": False,
            "compression_level": 9,
            "execution_must_bind_compressed_sha256": True,
            "flg": 0,
            "forbid_concatenated_members": True,
            "forbid_extra_field": True,
            "forbid_filename": True,
            "forbid_header_comment": True,
            "forbid_trailing_bytes": True,
            "mtime": 0,
            "require_crc32_and_isize": True,
            "streaming_decompression_maximum_bytes": REGISTRY_SIZE_BYTES,
        },
        "reference_observation_non_normative": {
            "compressed_sha256_windows_python_3_10": "3268402294630434a426b4a9b61ecc2d938bfba43e4a66a92f690e8aa251df16",
            "compressed_size_bytes_windows_python_3_10": 4_781_507,
            "current_runtime_round_trip": True,
            "current_runtime_transient_size_bytes": len(transient),
            "reason_non_normative": "GZIP_CONTAINER_BYTES_CAN_VARY_BY_COMPRESSOR_AND_OS_HEADER;_DECOMPRESSED_SOURCE_IDENTITY_IS_NORMATIVE",
        },
        "schema_id": "LOOP_CONTROL_REGISTRY_LEGACY_BYTE_CUSTODY_CONTRACT_20260711_v1",
        "source_identity": {
            "git_blob": REGISTRY_GIT_BLOB,
            "path": REGISTRY_PATH,
            "sha256": REGISTRY_SHA256,
            "size_bytes": REGISTRY_SIZE_BYTES,
            "source_commit": SOURCE_COMMIT,
        },
        "status": "LOSSLESS_CUSTODY_CONTRACT_PREPARED_NO_CUSTODY_PAYLOAD_OR_MIGRATION_EXECUTION",
    }


def _projection_schema_contract() -> dict[str, Any]:
    return {
        "additional_properties_allowed": False,
        "maximum_bytes_exclusive": 1_048_576,
        "required_top_level_fields": [
            "schema_id",
            "projection_version",
            "status",
            "source_legacy_identity",
            "history_index_pointer",
            "scientific_authority",
            "maintenance_authority",
            "active_scientific_workstream",
            "active_blockers",
            "claim_ceiling",
            "nonpromotion_assertions",
            "current_artifacts",
        ],
        "serialization": "CANONICAL_SORTED_UTF8_NO_BOM_LF_TERMINAL_NEWLINE_FINITE_JSON",
        "recursive_additional_properties_allowed": False,
        "source_mappings": {
            "active_blockers": {
                "emit": "ROW_ID_STATUS_AND_EVIDENCE_POINTER_ONLY_NO_FULL_ROW_PAYLOAD",
                "include_statuses": ["blocked", "missing", "not_assessed", "partial"],
                "row_arrays": ["pillar_readiness_rows", "seam_readiness_rows"],
                "source_git_blob": "85711a7c8cb0bc6a1f77d85cf3873726a5d6aa22",
                "source_path": "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json",
                "source_sha256": "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
            },
            "active_scientific_workstream": {
                "source_pointer": "/active_workstreams/0",
                "source_registry_sha256": REGISTRY_SHA256,
            },
            "claim_ceiling": {
                "source_pointers": [
                    "/active_workstreams/0/claim_ceiling_level",
                    "/active_workstreams/0/claim_status",
                    "/active_workstreams/0/strict_packet_result",
                ]
            },
            "maintenance_authority": {
                "source_path": "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json",
                "source_sha256": MAINTENANCE_AUTHORITY_SHA256,
            },
            "nonpromotion_assertions": {
                "source_boolean_or_no_fields": [
                    "/active_workstreams/0/unit_closure_claimed",
                    "/active_workstreams/0/pillar_or_seam_admissibility_claimed",
                    "/active_workstreams/0/level_four_or_five_authorized",
                    "/active_workstreams/0/physical_calibration_authorized",
                    "/active_workstreams/0/cross_sector_coupling_claim_authorized",
                    "/active_workstreams/0/C_k_action_embedding_authorized",
                    "/active_workstreams/0/ccft_resumed",
                    "/active_workstreams/0/master_action_promoted",
                ],
                "required_source_value": "no",
            },
            "scientific_authority": {
                "source_pointer": "/current_projection_v0",
                "source_registry_sha256": REGISTRY_SHA256,
            },
        },
    }


@lru_cache(maxsize=1)
def build_packet() -> dict[str, Any]:
    _verify_external_inputs()
    commitments = record_commitments()
    consumer = build_consumer_source_map()
    custody = build_custody_contract()
    consumer_sha = _sha256(canonical_json_bytes(consumer))
    custody_sha = _sha256(canonical_json_bytes(custody))
    controls = [
        {
            "control_id": f"REGISTRY-V1-NC-{index:03d}",
            "expected_error_code": error,
            "implementation_status": "REQUIRED_EXECUTION_REGRESSION_NOT_RUN_BY_PREPARATION",
            "mutation": mutation,
            "v0_false_acceptance_regression": mutation in V0_FALSE_ACCEPTANCES,
        }
        for index, (mutation, error) in enumerate(CONTROL_SPECS, start=1)
    ]
    if len(controls) != len({row["expected_error_code"] for row in controls}):
        raise GuardrailV1Error("typed control error codes are not unique")
    if not set(V0_FALSE_ACCEPTANCES).issubset(
        {row["mutation"] for row in controls}
    ):
        raise GuardrailV1Error("v0 false acceptance regression omitted")

    return {
        "api_contract": {
            "history_lookup_loads_only_index_selected_shard": True,
            "integrity_verification_bypass_parameter_allowed": False,
            "missing_and_ambiguous_ids_raise_distinct_typed_errors": True,
            "read_api": [
                "load_current_projection()",
                "get_current_target()",
                "get_current_maintenance_target()",
                "get_current_workstream(workstream_id)",
                "get_historical_record(record_id)",
                "iter_historical_records(...)",
                "verify_registry_integrity()",
                "reconstruct_legacy_registry()",
            ],
            "read_module_separate_from_write_module": True,
            "write_contract": {
                "closed_history_mutation_api_exists": False,
                "current_projection_only": True,
                "expected_old_hash_required": True,
                "external_authority_evidence_required": True,
            },
        },
        "authorization": {
            "maintenance_target": MAINTENANCE_TARGET,
            "migration_execution_authorized": False,
            "next_action": "review_loop_control_registry_sharding_and_current_projection_guardrail_packet_v1",
            "scientific_target": SCIENTIFIC_TARGET,
        },
        "boundary": {
            "compatibility_custody_payload_created": False,
            "consumer_migration_started": False,
            "current_projection_generated": False,
            "history_index_generated": False,
            "history_shards_generated": False,
            "legacy_monolith_modified_or_retired": False,
            "maintenance_target_rotated": False,
            "production_reader_or_writer_api_created": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_artifacts_modified": False,
            "scientific_claim_or_blocker_movement": False,
            "scientific_target_rotated": False,
        },
        "canonical_history_contract": {
            "empty_shards_allowed": False,
            "index_additional_properties_allowed": False,
            "jsonl_line_contract": "ONE_COMPLETE_CANONICAL_OBJECT_UTF8_NO_BOM_LF_FINITE_NO_DUPLICATE_KEYS",
            "maximum_uncompressed_shard_bytes": 5_242_880,
            "range_contract": "CONTIGUOUS_NONOVERLAPPING_GAP_FREE_SORTED_RECORD_ID_RANGES",
            "shard_additional_properties_allowed": False,
            "shard_closed_and_immutable_after_creation": True,
            "unique_shard_ids_and_paths": True,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "consumer_source_map": {
            "consumer_count": consumer["consumer_count"],
            "path": str(CONSUMER_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "runtime_completeness_proved": False,
            "sha256": consumer_sha,
            "static_literal_external_path_count": consumer["discovery"]["literal_external_path_count"],
        },
        "current_projection_contract": _projection_schema_contract(),
        "external_trust_anchors": {
            "authority_commitment_sha256": commitments["authority_commitment_sha256"],
            "candidate_owned_expected_hashes_trusted": False,
            "current_authoritative_surfaces_git_blob": CURRENT_AUTHORITATIVE_SURFACES_GIT_BLOB,
            "current_authoritative_surfaces_path": "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md",
            "current_authoritative_surfaces_sha256": CURRENT_AUTHORITATIVE_SURFACES_SHA256,
            "fixture_repair_acceptance_sha256": FIXTURE_REPAIR_ACCEPTANCE_SHA256,
            "maintenance_authority_sha256": MAINTENANCE_AUTHORITY_SHA256,
            "rejected_v0_review_sha256": REJECTED_V0_REVIEW_SHA256,
            "source_registry_git_blob": REGISTRY_GIT_BLOB,
            "source_registry_sha256": REGISTRY_SHA256,
            "source_registry_size_bytes": REGISTRY_SIZE_BYTES,
            "technical_debt_baseline_v1_sha256": TECHNICAL_DEBT_BASELINE_V1_SHA256,
        },
        "legacy_byte_custody_contract": {
            "path": str(CUSTODY_CONTRACT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sha256": custody_sha,
        },
        "mirror_classification": {
            "/active_workstreams/0": "CURRENT_SCIENTIFIC_MIRROR_WITH_SOURCE_COPY_RETAINED_AS_HISTORY",
            "/current_projection_v0": "LEGACY_COMPATIBILITY_CONTAINER_NEVER_V1_AUTHORITY",
            "/current_target_state": "BULKY_HISTORICAL_MIRROR_CONTAINER_NEVER_V1_AUTHORITY",
            "/current_target_state/active_workstreams/0": "NESTED_COMPATIBILITY_MIRROR_NOT_INDEPENDENT_RECORD",
        },
        "negative_control_count": len(controls),
        "negative_controls": controls,
        "packet_id": "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v1",
        "record_accounting": commitments,
        "record_identity_contract": {
            "digest": "FULL_SHA256_64_HEX_NO_TRUNCATION",
            "independent_of_migrated_list_position": True,
            "independent_of_shard_placement": True,
            "prefix": "lcr1:",
            "preimage_fields": [
                "domain",
                "record_class",
                "source_path",
                "source_git_blob",
                "logical_key",
                "original_json_pointer",
                "payload_sha256",
                "identical_occurrence_ordinal",
            ],
        },
        "schema_id": "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v1",
        "status": "CORRECTIVE_V1_GUARDRAIL_PREPARED_NO_PRODUCTION_LAYOUT_API_CONSUMER_MIGRATION_OR_EXECUTION_AUTHORITY",
    }


def build_all() -> dict[Path, bytes]:
    consumer = canonical_json_bytes(build_consumer_source_map())
    custody = canonical_json_bytes(build_custody_contract())
    packet = canonical_json_bytes(build_packet())
    return {
        CONSUMER_MAP_PATH: consumer,
        CUSTODY_CONTRACT_PATH: custody,
        PACKET_PATH: packet,
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
    parser = argparse.ArgumentParser(description="Build or verify the corrective registry guardrail v1.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    artifacts = build_all()
    if args.check:
        mismatches = [
            str(path.relative_to(REPO_ROOT))
            for path, raw in artifacts.items()
            if not path.exists() or path.read_bytes() != raw
        ]
        if mismatches:
            raise GuardrailV1Error("registry guardrail v1 mismatch: " + ", ".join(mismatches))
        for path, raw in artifacts.items():
            print(f"registry_guardrail_v1: OK {path.name} sha256={_sha256(raw)}")
        return 0
    for path, raw in artifacts.items():
        _atomic_write(path, raw)
        print(f"registry_guardrail_v1: wrote {path} sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
