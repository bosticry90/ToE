"""Prepare the schema-derived Stage-A registry execution contract v2.

Preparation only.  This successor freezes the repository-rooted consumer
inventory contract, derives the hash graph from actual schema fields, and
proves satisfiable complete and post-generation-blocked lifecycle models.  It
does not change the blocked implementation, create a prototype root, execute
Stage A, or authorize Stage B, migration, cutover, or scientific promotion.
"""

from __future__ import annotations

import argparse
import base64
import binascii
from copy import deepcopy
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any, Final, Iterable

from jsonschema import Draft202012Validator

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution_packet_v1 as v1,
)


REPO_ROOT: Final = find_repo_root(Path(__file__))
SOURCE_COMMIT: Final = "81a3555a1f83a37ec01bacc247f45d1a5bfe8430"
SOURCE_TREE: Final = "e3c39c9024ceb90675dbd09f66f3d90fc042f808"
CAPTURED_AT_UTC: Final = "2026-07-12T00:00:00Z"

PACKET_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "20260712_v2.json"
)
CONTRACT_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260712_v2.json"
)
PACKET_PATH: Final = REPO_ROOT / PACKET_REL
CONTRACT_PATH: Final = REPO_ROOT / CONTRACT_REL

PACKET_TARGET: Final = (
    "prepare_loop_control_registry_sharding_read_only_prototype_execution_packet_v2"
)
REVIEW_TARGET: Final = (
    "review_loop_control_registry_sharding_read_only_prototype_execution_packet_v2"
)
EXECUTION_TARGET: Final = (
    "execute_loop_control_registry_sharding_read_only_prototype_v2"
)
EXECUTION_COMMAND: Final = (
    "python -m formal.python.tools."
    "loop_control_registry_sharding_read_only_prototype_execution "
    "--execute --contract-v2"
)
SCIENTIFIC_TARGET: Final = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET: Final = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)

REGISTRY_REL: Final = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
BASELINE_CONSUMER_REL: Final = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
V3_SCHEMAS_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3.json"
)
V3_PROTOCOL_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v3.json"
)
V1_PACKET_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "20260711_v1.json"
)
V1_CONTRACT_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v1.json"
)
V1_REVIEW_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v1.json"
)
CUSTODY_CONTRACT_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_LEGACY_BYTE_CUSTODY_CONTRACT_20260711_v1.json"
)
GUARDRAIL_PACKET_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_"
    "PACKET_20260711_v1.json"
)
GUARDRAIL_REVIEW_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_"
    "INDEPENDENT_REVIEW_20260711_v1.json"
)
MAINTENANCE_AUTHORITY_REL: Final = (
    "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
)
AUTHORITATIVE_SURFACES_REL: Final = (
    "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
REQUIREMENTS_REL: Final = "requirements.ci.lock"

ORCHESTRATOR_REL: Final = (
    "formal/python/tools/loop_control_registry_sharding_read_only_prototype_execution.py"
)
READER_REL: Final = "formal/python/toe/loop_control_registry_v1.py"
VALIDATOR_REL: Final = "formal/python/toe/loop_control_registry_v1_validator.py"
PRODUCTION_TEST_REL: Final = (
    "formal/python/tests/test_loop_control_registry_v1_production_controls.py"
)
AUTHORIZED_IMPLEMENTATION_PATHS: Final = [
    ORCHESTRATOR_REL,
    READER_REL,
    VALIDATOR_REL,
    PRODUCTION_TEST_REL,
]

PROTOTYPE_ROOT_REL: Final = "formal/scratch/loop_control_registry_v1_prototype"
PRODUCTION_LAYOUT_PATHS: Final = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    PROTOTYPE_ROOT_REL,
]

REGISTRY_SHA256: Final = (
    "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
)
AUTHORITY_COMMITMENT_SHA256: Final = (
    "fd4348411236648d6216900eced59524b87c561bfa0d36186cf4c4d19a2e6b34"
)
HISTORY_FULL_RECORD_IDENTITY_ROOT_SHA256: Final = (
    "67a23fda6348a2a6e12e4c2af775d115c692ecbe4d0650f0844a982d869e112d"
)
HISTORY_IDENTITY_PAYLOAD_POINTER_ROOT_SHA256: Final = (
    "a97799ea412006dde3c259b718b10aad9dee7012181611f3f1d5f1a1e821a967"
)
HISTORY_ORIGINAL_POINTER_SET_SHA256: Final = (
    "219f4bc866b731b74ef50a439b6a869d8add33c6c5ce8e83a621115c1649c6bf"
)
V1_PACKET_SHA256: Final = (
    "bbefe919ffe2f4bd55538fdcee83a29be4e2d17d3d82d5391dede6b097270854"
)
V1_CONTRACT_SHA256: Final = (
    "ef1d51cd4a9a55c6affe0d7273d183eb69326474d0d0ab904ea13544dac1adff"
)
V1_REVIEW_SHA256: Final = (
    "a81a157efa809630057ad3e8a639f41d8ef7335cd529c8cd2a92fbb45612e54c"
)

FROZEN_INPUT_PATHS: Final = [
    V1_PACKET_REL,
    V1_CONTRACT_REL,
    V1_REVIEW_REL,
    V3_SCHEMAS_REL,
    V3_PROTOCOL_REL,
    CUSTODY_CONTRACT_REL,
    GUARDRAIL_PACKET_REL,
    GUARDRAIL_REVIEW_REL,
    BASELINE_CONSUMER_REL,
    REGISTRY_REL,
    MAINTENANCE_AUTHORITY_REL,
    AUTHORITATIVE_SURFACES_REL,
    REQUIREMENTS_REL,
    *AUTHORIZED_IMPLEMENTATION_PATHS,
]

# sha256, Git object id, and byte count at SOURCE_COMMIT.  Keeping the complete
# tuples prevents a successor generator from silently accepting drift in a
# non-registry trust root.
EXPECTED_INPUTS: Final[dict[str, tuple[str, str, int]]] = {
    V1_PACKET_REL: (V1_PACKET_SHA256, "d8b040ce202781fc65b28015e0917f2d0c272817", 2430),
    V1_CONTRACT_REL: (V1_CONTRACT_SHA256, "737c74f7ac66f145c347cd621e1fb9a6d03b8a39", 439612),
    V1_REVIEW_REL: (V1_REVIEW_SHA256, "26d5023078c694d81cb79a0b637c29481612b8c4", 21909),
    V3_SCHEMAS_REL: ("86289bf922d60c3320f040779a6043cdb3f2acf3d5393ce7503ef9d3375f6cde", "eaf40d9fc8c6bd9364c2f016a19b3dc4f7b1d646", 438862),
    V3_PROTOCOL_REL: ("ad65ceb56d3b284b3a55e433afc13745c3c574c9f2e7bf0fe367172924ea08e2", "8d87fe5ddf9446296b71ace196d33b1c2e629ed5", 187789),
    CUSTODY_CONTRACT_REL: ("bc35c992c9b9fd7dd9c2e84ed6d5b89463b3ce8eb13dc2f7c7d1c539b4d23ce9", "c2d47dd22e6c81180bae5d7e00e04b0121d12cf3", 1918),
    GUARDRAIL_PACKET_REL: ("41994b0c1703d7f7f7ff7aeda217900a3136489f070ae55a88f2db10a13d12c0", "83069c2d254947176121dd9e9a4def0b9efd23b9", 23432),
    GUARDRAIL_REVIEW_REL: ("4b99d6d3801a8bbd2f918311116dfdfce8ef595f7c0e1b629bc3595820612dca", "90b0660e2c6108c5b8193c77a6c8400e9ebafb52", 4572),
    BASELINE_CONSUMER_REL: ("5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642", "9f9846ba735813c5b2b18f7a0115d88230a36600", 469583),
    REGISTRY_REL: (REGISTRY_SHA256, "e6c5b3773dccd92fde9c0a8d486a56f993d6b235", 52340650),
    MAINTENANCE_AUTHORITY_REL: ("ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b", "dca311d6abe38a872495c07f302d13ad886c0232", 1768),
    AUTHORITATIVE_SURFACES_REL: ("cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248", "d46c5fb1966dcefc6b923776b7d94c4f5009b889", 714575),
    REQUIREMENTS_REL: ("79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b", "bcc393883b90739408ed14d53d57dd0b42d0c2bd", 741),
    ORCHESTRATOR_REL: ("59e4c47674ad0f00ddccaf978ea420b8495c8f16d67529639ec5527cf863fae7", "1ad5d758f727d3f705f4977b7f02a0400ca9b8d6", 11589),
    READER_REL: ("699f85df13d3023711b56be842a2124067b5620af24407aa691301ec7951380d", "5d0bf0c293796e6576267a128369ae84c2481191", 34616),
    VALIDATOR_REL: ("149779b8c13ffda4be332f6b871f64bf88819e4c2c3b0302bbeb5e578463a3b2", "8d1428a5f4f92358f09b16d2b65dff6826467b02", 82650),
    PRODUCTION_TEST_REL: ("fb2396bc1df11bbddd5b5e65eb74700694734ab49968d3d897d14cf779a0a6eb", "a664297cf8ece147b1a9783b5500fb76843174db", 15340),
}

NONLITERAL_READERS: Final = [
    "formal/python/tests/test_loop_control_registry_envelope_integrity_gate.py",
    "formal/python/tests/test_loop_control_registry_integrity_repair_custody_gate.py",
    "formal/python/tools/loop_control_registry_sharding_guardrail.py",
]

CONSUMER_CATEGORIES: Final = [
    "DIRECT_READER",
    "INDIRECT_API_CONSUMER",
    "DYNAMIC_READER",
    "WRITER",
    "TEST_ONLY",
    "DOCUMENTATION_ONLY",
    "HISTORICAL_ONLY",
    "GENERATED_REFERENCE",
]
OPERATION_CLASSES: Final = [
    "READ_CURRENT_AUTHORITY",
    "READ_HISTORICAL_RECORD",
    "ITERATE_WORKSTREAMS",
    "VALIDATE_ROOT_SCHEMA",
    "MUTATE_REGISTRY",
    "GENERATE_MIRROR",
    "COMPARE_HASH",
    "LITERAL_REFERENCE_ONLY",
]
DISCOVERY_MECHANISMS: Final = [
    "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE",
    "REVIEWED_NONLITERAL_PATH_RULE",
]
RUNTIME_REQUIRED_CATEGORIES: Final = [
    "DIRECT_READER",
    "INDIRECT_API_CONSUMER",
    "DYNAMIC_READER",
    "WRITER",
]


class V2PreparationError(ValueError):
    """The reviewed v2 preparation model is inconsistent."""

    def __init__(self, message: str) -> None:
        super().__init__(message)
        self.code = message.split(":", 1)[0] if message.startswith(("V1-E-", "V2-E-")) else None


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def compact_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            indent=2,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _strict_json(raw: bytes) -> Any:
    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise V2PreparationError(f"duplicate JSON key: {key}")
            output[key] = value
        return output

    def reject_constant(value: str) -> Any:
        raise V2PreparationError(f"nonfinite JSON constant: {value}")

    return json.loads(raw, object_pairs_hook=pairs_hook, parse_constant=reject_constant)


def _git_blob(commit: str, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise V2PreparationError(f"missing Git input: {commit}:{relative}")
    return result.stdout


def _git_blobs(commit: str, relatives: Iterable[str]) -> dict[str, bytes]:
    """Read many Git blobs through one ordered cat-file batch."""

    paths = sorted(set(relatives))
    result = subprocess.run(
        ["git", "cat-file", "--batch"],
        cwd=REPO_ROOT,
        input="".join(f"{commit}:{path}\n" for path in paths).encode("utf-8"),
        capture_output=True,
        check=True,
    )
    output: dict[str, bytes] = {}
    cursor = 0
    for path in paths:
        header_end = result.stdout.find(b"\n", cursor)
        if header_end < 0:
            raise V2PreparationError("V2-E-CONSUMER-GIT-BATCH-TRUNCATED")
        header = result.stdout[cursor:header_end].decode("ascii").split()
        if len(header) != 3 or header[1] != "blob":
            raise V2PreparationError("V2-E-CONSUMER-GIT-BATCH-MISSING")
        size = int(header[2])
        start = header_end + 1
        end = start + size
        if end >= len(result.stdout) or result.stdout[end : end + 1] != b"\n":
            raise V2PreparationError("V2-E-CONSUMER-GIT-BATCH-TRUNCATED")
        output[path] = result.stdout[start:end]
        cursor = end + 1
    if cursor != len(result.stdout):
        raise V2PreparationError("V2-E-CONSUMER-GIT-BATCH-TRAILING")
    return output


_SOURCE_REGISTRY_BYTES_CACHE: bytes | None = None
_CUSTODY_PAYLOAD_BYTES_CACHE: bytes | None = None


def _source_registry_bytes() -> bytes:
    """Return the reviewed Git object's exact registry bytes."""

    global _SOURCE_REGISTRY_BYTES_CACHE
    if _SOURCE_REGISTRY_BYTES_CACHE is None:
        raw = _git_blob(SOURCE_COMMIT, REGISTRY_REL)
        if sha256(raw) != REGISTRY_SHA256 or len(raw) != 52_340_650:
            raise V2PreparationError("V1-E-EXTERNAL-TRUST-ROOT-REBIND")
        _SOURCE_REGISTRY_BYTES_CACHE = raw
    return _SOURCE_REGISTRY_BYTES_CACHE


def _custody_payload_bytes() -> bytes:
    """Build the deterministic RFC-1952 custody member used by the witness."""

    global _CUSTODY_PAYLOAD_BYTES_CACHE
    if _CUSTODY_PAYLOAD_BYTES_CACHE is None:
        compressed = gzip.compress(
            _source_registry_bytes(), compresslevel=9, mtime=0
        )
        # RFC 1952 OS is metadata, not compressed content.  The reviewed
        # profile fixes it to 255 across Python/zlib platforms.
        compressed = compressed[:9] + b"\xff" + compressed[10:]
        if (
            compressed[:3] != b"\x1f\x8b\x08"
            or compressed[3] != 0
            or compressed[4:8] != b"\0\0\0\0"
            or compressed[8] != 2
            or compressed[9] != 255
            or gzip.decompress(compressed) != _source_registry_bytes()
        ):
            raise V2PreparationError("V2-E-CUSTODY-RECONSTRUCTION-MISMATCH")
        _CUSTODY_PAYLOAD_BYTES_CACHE = compressed
    return _CUSTODY_PAYLOAD_BYTES_CACHE


_HISTORY_WITNESS_CACHE: dict[str, Any] | None = None
_HISTORY_WITNESS_SCHEMA_VALIDATED = False


def _pointer_token(value: str) -> str:
    return value.replace("~", "~0").replace("/", "~1")


def _payload_kind(value: Any) -> str:
    if value is None:
        return "NULL"
    if isinstance(value, bool):
        return "BOOLEAN"
    if isinstance(value, (int, float)):
        return "NUMBER"
    if isinstance(value, str):
        return "STRING"
    if isinstance(value, list):
        return "ARRAY"
    return "OBJECT"


def _history_witness(
    schema: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Build the exact 4,691-record history and deterministic shard set."""

    global _HISTORY_WITNESS_CACHE, _HISTORY_WITNESS_SCHEMA_VALIDATED
    if _HISTORY_WITNESS_CACHE is None:
        registry = _strict_json(_source_registry_bytes())
        if not isinstance(registry, dict) or not isinstance(
            registry.get("workstreams"), list
        ):
            raise V2PreparationError("V2-E-HISTORY-SOURCE-SHAPE-MISMATCH")
        source_blob = EXPECTED_INPUTS[REGISTRY_REL][1]
        source_rows: list[tuple[str, str, str, Any]] = []
        for key, payload in registry.items():
            if key != "workstreams":
                source_rows.append(
                    (
                        "ROOT_FIELD",
                        key,
                        f"/{_pointer_token(key)}",
                        payload,
                    )
                )
        for index, payload in enumerate(registry["workstreams"]):
            if not isinstance(payload, dict):
                raise V2PreparationError(
                    "V2-E-HISTORY-SOURCE-SHAPE-MISMATCH"
                )
            logical_key = str(
                payload.get("workstream_id")
                or payload.get("id")
                or payload.get("target")
                or f"anonymous_workstream_{index}"
            )
            source_rows.append(
                (
                    "WORKSTREAM",
                    logical_key,
                    f"/workstreams/{index}",
                    payload,
                )
            )

        occurrences: dict[tuple[str, str, str], int] = {}
        records: list[dict[str, Any]] = []
        identity_rows: list[str] = []
        pointers: list[str] = []
        for record_class, logical_key, pointer, payload in source_rows:
            payload_raw = compact_json_bytes(payload)
            payload_sha = sha256(payload_raw)
            occurrence_key = (record_class, logical_key, payload_sha)
            ordinal = occurrences.get(occurrence_key, 0)
            occurrences[occurrence_key] = ordinal + 1
            preimage = {
                "domain": "LOOP_CONTROL_RECORD_ID_v1",
                "record_class": record_class,
                "source_path": REGISTRY_REL,
                "source_git_blob": source_blob,
                "logical_key": logical_key,
                "original_json_pointer": pointer,
                "payload_sha256": payload_sha,
                "identical_occurrence_ordinal": ordinal,
            }
            record_id = "lcr1:" + sha256(compact_json_bytes(preimage))
            records.append(
                {
                    "identical_occurrence_ordinal": ordinal,
                    "logical_key": logical_key,
                    "original_json_pointer": pointer,
                    "payload_canonical_json_utf8_base64": (
                        base64.b64encode(payload_raw).decode("ascii")
                    ),
                    "payload_kind": _payload_kind(payload),
                    "payload_sha256": payload_sha,
                    "payload_size_bytes": len(payload_raw),
                    "record_class": record_class,
                    "record_id": record_id,
                    "record_version": 1,
                    "schema_id": "LOOP_CONTROL_HISTORY_RECORD_v1",
                    "source_git_blob": source_blob,
                    "source_path": REGISTRY_REL,
                }
            )
            identity_rows.append(f"{record_id}:{payload_sha}:{pointer}")
            pointers.append(pointer)
        records.sort(key=lambda row: row["record_id"].encode("utf-8"))
        record_ids = [row["record_id"] for row in records]
        authority_payload = {
            "active_workstream_sha256": sha256(
                compact_json_bytes(
                    registry.get("active_workstreams", [None])[0]
                )
            ),
            "legacy_current_projection": registry.get(
                "current_projection_v0"
            ),
            "maintenance_authority": _strict_json(
                _git_blob(SOURCE_COMMIT, MAINTENANCE_AUTHORITY_REL)
            ),
        }
        if (
            len(records) != 4_691
            or len([row for row in records if row["record_class"] == "ROOT_FIELD"])
            != 4_152
            or len([row for row in records if row["record_class"] == "WORKSTREAM"])
            != 539
            or sha256("\n".join(record_ids).encode("utf-8"))
            != HISTORY_FULL_RECORD_IDENTITY_ROOT_SHA256
            or sha256("\n".join(sorted(identity_rows)).encode("utf-8"))
            != HISTORY_IDENTITY_PAYLOAD_POINTER_ROOT_SHA256
            or sha256("\n".join(sorted(pointers)).encode("utf-8"))
            != HISTORY_ORIGINAL_POINTER_SET_SHA256
            or sha256(compact_json_bytes(authority_payload))
            != AUTHORITY_COMMITMENT_SHA256
        ):
            raise V2PreparationError("V2-E-HISTORY-EXTERNAL-ROOT-MISMATCH")

        shards: list[list[dict[str, Any]]] = []
        shard_lines: list[list[bytes]] = []
        current_records: list[dict[str, Any]] = []
        current_lines: list[bytes] = []
        current_size = 0
        for record in records:
            line = compact_json_bytes(record) + b"\n"
            if current_lines and current_size + len(line) > 5_242_880:
                shards.append(current_records)
                shard_lines.append(current_lines)
                current_records = []
                current_lines = []
                current_size = 0
            current_records.append(record)
            current_lines.append(line)
            current_size += len(line)
        if current_lines:
            shards.append(current_records)
            shard_lines.append(current_lines)

        members: dict[str, bytes] = {}
        descriptors: list[dict[str, Any]] = []
        for sequence_index, (shard_records, lines) in enumerate(
            zip(shards, shard_lines, strict=True)
        ):
            path = (
                "history/shards/"
                f"LOOP_CONTROL_HISTORY_{sequence_index:04d}.jsonl"
            )
            shard_raw = b"".join(lines)
            ids = [row["record_id"] for row in shard_records]
            descriptor = {
                "closed": True,
                "first_record_id": ids[0],
                "last_record_id": ids[-1],
                "path": path,
                "record_count": len(ids),
                "record_id_root_sha256": sha256(
                    "\n".join(ids).encode("utf-8")
                ),
                "sequence_index": sequence_index,
                "sha256": sha256(shard_raw),
                "shard_id": "",
                "uncompressed_size_bytes": len(shard_raw),
            }
            shard_preimage = {
                "domain": "LOOP_CONTROL_SHARD_ID_v1",
                **{
                    key: descriptor[key]
                    for key in (
                        "sequence_index",
                        "path",
                        "first_record_id",
                        "last_record_id",
                        "record_count",
                        "record_id_root_sha256",
                        "sha256",
                        "uncompressed_size_bytes",
                    )
                },
            }
            descriptor["shard_id"] = "lcs1:" + sha256(
                compact_json_bytes(shard_preimage)
            )
            members[path] = shard_raw
            descriptors.append(descriptor)
        member_rows = [
            {
                "path": descriptor["path"],
                "sha256": descriptor["sha256"],
                "size_bytes": descriptor["uncompressed_size_bytes"],
            }
            for descriptor in descriptors
        ]
        set_bytes = (
            b"LOOP_CONTROL_HISTORY_SHARD_ARTIFACT_SET_v2\0"
            + b"\n".join(compact_json_bytes(row) for row in member_rows)
        )
        _HISTORY_WITNESS_CACHE = {
            "descriptors": descriptors,
            "members": members,
            "records": records,
            "representative_record": min(
                records, key=lambda row: len(compact_json_bytes(row))
            ),
            "records_by_shard": shards,
            "set_bytes": set_bytes,
        }
    if schema is not None and not _HISTORY_WITNESS_SCHEMA_VALIDATED:
        validator = Draft202012Validator(schema)
        for record in _HISTORY_WITNESS_CACHE["records"]:
            validator.validate(record)
        _HISTORY_WITNESS_SCHEMA_VALIDATED = True
    return _HISTORY_WITNESS_CACHE


def _git_oid(commit: str, relative: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _git_path_exists(commit: str, relative: str) -> bool:
    return (
        subprocess.run(
            ["git", "cat-file", "-e", f"{commit}:{relative}"],
            cwd=REPO_ROOT,
            capture_output=True,
            check=False,
        ).returncode
        == 0
    )


def _git_binding(relative: str) -> dict[str, Any]:
    raw = _git_blob(SOURCE_COMMIT, relative)
    return {
        "git_blob": _git_oid(SOURCE_COMMIT, relative),
        "path": relative,
        "sha256": sha256(raw),
        "size_bytes": len(raw),
        "source_commit": SOURCE_COMMIT,
    }


def _frozen_input_bindings() -> dict[str, dict[str, Any]]:
    bindings = {path: _git_binding(path) for path in FROZEN_INPUT_PATHS}
    if set(bindings) != set(EXPECTED_INPUTS):
        raise V2PreparationError("V2-E-FROZEN-INPUT-CATALOG")
    for path, (expected_sha, expected_oid, expected_size) in EXPECTED_INPUTS.items():
        row = bindings[path]
        if (row["sha256"], row["git_blob"], row["size_bytes"]) != (
            expected_sha,
            expected_oid,
            expected_size,
        ):
            raise V2PreparationError(f"frozen predecessor drift: {path}")
    return bindings


def _closed(
    properties: dict[str, Any], required: list[str] | None = None
) -> dict[str, Any]:
    return {
        "additionalProperties": False,
        "properties": properties,
        "required": list(properties) if required is None else required,
        "type": "object",
    }


def _sha_schema(
    target: str,
    *,
    semantics: str = "CONTENT_SHA256",
    resolver: str = "FIXED_ARTIFACT_TYPE",
) -> dict[str, Any]:
    return {
        "pattern": "^[0-9a-f]{64}$",
        "type": "string",
        "x-toe-hash-edge": {
            "hash_semantics": semantics,
            "referenced_artifact_type": target,
            "target_resolver": resolver,
        },
    }


def _is_hash_bearing_schema_field(name: str, schema: Any) -> bool:
    """Recognize SHA-256 leaves independently of one schema spelling."""

    if not isinstance(schema, dict):
        return False
    constant = schema.get("const")
    constant_is_sha256 = (
        isinstance(constant, str)
        and len(constant) == 64
        and all(character in "0123456789abcdef" for character in constant)
    )
    return (
        name == "sha256"
        or name.endswith("_sha256")
        or schema.get("pattern") == "^[0-9a-f]{64}$"
        or constant_is_sha256
    )


def _commit_schema() -> dict[str, Any]:
    return {"pattern": "^[0-9a-f]{40}$", "type": "string"}


def _path_schema() -> dict[str, Any]:
    return {
        "maxLength": 240,
        "minLength": 1,
        "pattern": (
            r"^(?!/)(?!.*//)(?![.]{1,2}(?:/|$))"
            r"(?!.*(?:/[.]{1,2})(?:/|$))(?!.*[\\:\x00-\x1f*?<>|\"])"
            r"(?![^/]*[. ](?:/|$))(?!.*[/][^/]*[. ](?:/|$))[^/]+(?:/[^/]+)*$"
        ),
        "type": "string",
    }


def _identity_schema(target: str) -> dict[str, Any]:
    return _closed(
        {
            "path": _path_schema(),
            "sha256": _sha_schema(target),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )


def _git_identity_schema(target: str) -> dict[str, Any]:
    return _closed(
        {
            "git_blob": _commit_schema(),
            "git_commit": _commit_schema(),
            "path": _path_schema(),
            "sha256": _sha_schema(target),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )


def _consumer_row_schema() -> dict[str, Any]:
    return _closed(
        {
            "baseline_delta_class": {
                "enum": ["ADDED", "CHANGED", "UNCHANGED"],
                "type": "string",
            },
            "byte_end": {"minimum": 1, "type": "integer"},
            "byte_start": {"minimum": 0, "type": "integer"},
            "consumer_category": {"enum": CONSUMER_CATEGORIES, "type": "string"},
            "consumer_id": {
                "pattern": "^lcc2:[0-9a-f]{64}$",
                "type": "string",
            },
            "discovery_mechanism": {
                "enum": DISCOVERY_MECHANISMS,
                "type": "string",
            },
            "git_blob": _commit_schema(),
            "operation_class": {"enum": OPERATION_CLASSES, "type": "string"},
            "path": _path_schema(),
            "runtime_required": {"type": "boolean"},
            "scan_observation_sha256": _sha_schema(
                "REPOSITORY_CONSUMER_SCAN_OBSERVATION",
                semantics="MEMBER_CONTENT_SHA256",
                resolver="SIBLING_CONSUMER_ID",
            ),
            "source_sha256": _sha_schema(
                "REPOSITORY_CONSUMER_SOURCE",
                semantics="MEMBER_CONTENT_SHA256",
                resolver="SIBLING_CONSUMER_ID",
            ),
            "statement_or_call_site_sha256": _sha_schema(
                "REPOSITORY_CONSUMER_STATEMENT",
                semantics="MEMBER_CONTENT_SHA256",
                resolver="SIBLING_CONSUMER_ID",
            ),
        }
    )


ARTIFACT_PHASES: Final[dict[str, tuple[str, int, str]]] = {
    # External roots and logical preimages.
    "ACCEPTED_V2_INDEPENDENT_REVIEW": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "AUTHORIZED_IMPLEMENTATION": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "AUTHORITY_EVIDENCE": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "BASELINE_CONSUMER_SOURCE_MAP": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "CONTROL_PROFILE": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "CUSTODY_CONTRACT": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "EXECUTION_PROTOCOL": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "GUARDRAIL_PACKET": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "GUARDRAIL_REVIEW": ("REVIEWED_CONTRACT", 0, "EXTERNAL"),
    "REPOSITORY_CONSUMER_SOURCE": ("REPOSITORY_SCAN", 1, "EXTERNAL"),
    "REPOSITORY_CONSUMER_STATEMENT": ("REPOSITORY_SCAN", 2, "EXTERNAL"),
    "REPOSITORY_CONSUMER_SCAN_OBSERVATION": (
        "REPOSITORY_SCAN",
        2,
        "EXTERNAL",
    ),
    "SOURCE_AUTHORITY_COMMITMENT": ("REPOSITORY_SCAN", 3, "EXTERNAL"),
    "SOURCE_CURRENT_ARTIFACT": ("REPOSITORY_SCAN", 4, "EXTERNAL"),
    "SOURCE_REGISTRY": ("REPOSITORY_SCAN", 5, "EXTERNAL"),
    "SOURCE_REGISTRY_OPERATION_RESULT": ("REPOSITORY_SCAN", 6, "LOGICAL_SET"),
    "SOURCE_REGISTRY_RECORD_PAYLOAD": ("REPOSITORY_SCAN", 7, "LOGICAL_SET"),
    "V2_CONTRACT": ("REVIEWED_CONTRACT", 8, "EXTERNAL"),
    "V2_SCHEMA_BUNDLE": ("REVIEWED_CONTRACT", 9, "LOGICAL_SET"),
    "PREFLIGHT_CONSUMER_IDENTITY_SET": ("PREFLIGHT_SCAN", 10, "LOGICAL_SET"),
    "PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET": (
        "PREFLIGHT_SCAN",
        11,
        "LOGICAL_SET",
    ),
    "BASELINE_DELTA_SET": ("PREFLIGHT_SCAN", 12, "LOGICAL_SET"),
    "PRE_RUN_INVENTORY_SET": ("PREFLIGHT_SCAN", 12, "LOGICAL_SET"),
    "ALLOWED_OUTPUT_PATH_SET": ("REVIEWED_CONTRACT", 12, "EXTERNAL"),
    "PREFLIGHT_CONSUMER_INVENTORY": ("PREFLIGHT_SCAN", 13, "ARTIFACT"),
    "EXECUTION_PREFLIGHT_ATTESTATION": (
        "PREFLIGHT_ATTESTATION",
        14,
        "ARTIFACT",
    ),
    "SOURCE_MANIFEST": ("SOURCE_MANIFEST", 20, "ARTIFACT"),
    "CONSUMER_MAP": ("CANDIDATE_PAYLOADS", 30, "ARTIFACT"),
    "CUSTODY_PAYLOAD": ("CANDIDATE_PAYLOADS", 31, "ARTIFACT"),
    "HISTORY_SHARD": ("CANDIDATE_PAYLOADS", 32, "ARTIFACT_SET"),
    "CUSTODY_MANIFEST": ("CANDIDATE_BINDINGS", 33, "ARTIFACT"),
    "LEGACY_RECONSTRUCTED_BYTES": ("CANDIDATE_BINDINGS", 34, "LOGICAL_SET"),
    "LEGACY_RECONSTRUCTION": ("CANDIDATE_BINDINGS", 35, "ARTIFACT"),
    "HISTORY_SHARD_RECORD_ID_SET": (
        "CANDIDATE_BINDINGS",
        36,
        "LOGICAL_SET",
    ),
    "HISTORY_FULL_RECORD_IDENTITY_SET": (
        "CANDIDATE_BINDINGS",
        36,
        "LOGICAL_SET",
    ),
    "HISTORY_IDENTITY_PAYLOAD_POINTER_SET": (
        "CANDIDATE_BINDINGS",
        36,
        "LOGICAL_SET",
    ),
    "HISTORY_ORIGINAL_POINTER_SET": (
        "CANDIDATE_BINDINGS",
        36,
        "LOGICAL_SET",
    ),
    "HISTORY_INDEX": ("CANDIDATE_INDEX", 37, "ARTIFACT"),
    "CURRENT_PROJECTION": ("CANDIDATE_PROJECTION", 38, "ARTIFACT"),
    "CURRENT_PROJECTION_OPERATION_RESULT": (
        "CANDIDATE_PROJECTION",
        39,
        "LOGICAL_SET",
    ),
    "RUNTIME_TRACE": ("CANDIDATE_RUNTIME_EVIDENCE", 41, "ARTIFACT"),
    "RUNTIME_TRACE_MANIFEST": (
        "CANDIDATE_RUNTIME_EVIDENCE",
        42,
        "ARTIFACT",
    ),
    "REVIEWED_TRUST_ANCHORS": ("CANDIDATE_CONTROLS", 43, "ARTIFACT"),
    "ROLLBACK_INVENTORY": ("CANDIDATE_CONTROLS", 44, "ARTIFACT"),
    "WRITER_PROBE": ("CANDIDATE_CONTROLS", 45, "ARTIFACT"),
    "CORE_CANDIDATE_ARTIFACT_SET": ("CANDIDATE_CONTROLS", 46, "LOGICAL_SET"),
    "EXECUTION_STREAM": ("CANDIDATE_CONTROLS", 47, "LOGICAL_SET"),
    "CONTROL_RESULT_SET": ("CANDIDATE_CONTROLS", 48, "LOGICAL_SET"),
    "VALIDATION_REPORT": ("CANDIDATE_CONTROLS", 49, "ARTIFACT"),
    "CONTROL_EVIDENCE": ("CANDIDATE_CONTROLS", 50, "ARTIFACT"),
    "ALL_CANDIDATE_ARTIFACT_SET": ("CANDIDATE_FINALIZATION", 51, "LOGICAL_SET"),
    "RUNTIME_MANIFEST": ("RUNTIME_MANIFEST", 60, "ARTIFACT"),
    "EXECUTION_REPORT": ("EXECUTION_REPORT", 70, "ARTIFACT"),
    "TERMINAL_ENVELOPE": ("TERMINAL_ENVELOPE", 80, "ARTIFACT"),
    "INDEPENDENT_REVIEW_IDENTITY_SET": (
        "INDEPENDENT_REVIEW_RESCAN",
        90,
        "LOGICAL_SET",
    ),
    "INDEPENDENT_REVIEW_RUNTIME_REQUIRED_SET": (
        "INDEPENDENT_REVIEW_RESCAN",
        90,
        "LOGICAL_SET",
    ),
    "INDEPENDENT_REVIEW_BASELINE_DELTA_SET": (
        "INDEPENDENT_REVIEW_RESCAN",
        90,
        "LOGICAL_SET",
    ),
    "INDEPENDENT_REVIEW_CONSUMER_INVENTORY": (
        "INDEPENDENT_REVIEW_RESCAN",
        91,
        "ARTIFACT",
    ),
    "INDEPENDENT_REVIEW": ("INDEPENDENT_REVIEW", 92, "ARTIFACT"),
}

ARTIFACT_BRANCHES: Final = {
    artifact: ("COMPLETE", "POST_GENERATION_BLOCKED")
    for artifact, (_, _, kind) in ARTIFACT_PHASES.items()
    if kind in {"ARTIFACT", "ARTIFACT_SET"}
}


def _custom_runtime_schemas() -> dict[str, dict[str, Any]]:
    draft = "https://json-schema.org/draft/2020-12/schema"
    row = _consumer_row_schema()
    count = {"minimum": 0, "type": "integer"}
    inventory = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_EXECUTION_PREFLIGHT_CONSUMER_INVENTORY_v2",
                "type": "string",
            },
            "inventory_origin": {
                "enum": ["REPOSITORY_GIT_OBJECT_SCAN", "INDEPENDENT_REVIEW_GIT_OBJECT_RESCAN"],
                "type": "string",
            },
            "algorithm_id": {
                "const": "LOOP_CONTROL_CONSUMER_DISCOVERY_CALLSITE_v2",
                "type": "string",
            },
            "scanner_implementation_id": {
                "enum": [
                    "EXECUTION_GIT_GREP_CAT_FILE_SCANNER_v2",
                    "INDEPENDENT_REVIEW_FULL_TREE_CAT_FILE_SCANNER_v2",
                ],
                "type": "string",
            },
            "source_commit": _commit_schema(),
            "source_tree": _commit_schema(),
            "consumers": {"items": row, "type": "array", "uniqueItems": True},
            "consumer_identity_count": count,
            "consumer_identity_root_sha256": _sha_schema(
                "PREFLIGHT_CONSUMER_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "runtime_required_count": count,
            "runtime_required_identity_root_sha256": _sha_schema(
                "PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "nonruntime_count": count,
            "unique_path_count": count,
            "baseline_delta_rows": {
                "items": _closed(
                    {
                        "classification": {
                            "enum": ["ADDED", "CHANGED", "REMOVED"],
                            "type": "string",
                        },
                        "path": _path_schema(),
                    }
                ),
                "type": "array",
                "uniqueItems": True,
            },
            "baseline_delta_root_sha256": _sha_schema(
                "BASELINE_DELTA_SET", semantics="ORDERED_DELTA_SET_ROOT"
            ),
        }
    )
    review_inventory = deepcopy(inventory)
    review_inventory["properties"]["schema_id"] = {
        "const": "LOOP_CONTROL_INDEPENDENT_REVIEW_CONSUMER_INVENTORY_v2",
        "type": "string",
    }
    review_inventory["properties"]["inventory_origin"] = {
        "const": "INDEPENDENT_REVIEW_GIT_OBJECT_RESCAN",
        "type": "string",
    }
    review_inventory["properties"]["scanner_implementation_id"] = {
        "const": "INDEPENDENT_REVIEW_FULL_TREE_CAT_FILE_SCANNER_v2",
        "type": "string",
    }
    review_inventory["properties"]["consumer_identity_root_sha256"] = _sha_schema(
        "INDEPENDENT_REVIEW_IDENTITY_SET", semantics="ORDERED_IDENTITY_SET_ROOT"
    )
    review_inventory["properties"]["runtime_required_identity_root_sha256"] = _sha_schema(
        "INDEPENDENT_REVIEW_RUNTIME_REQUIRED_SET",
        semantics="ORDERED_IDENTITY_SET_ROOT",
    )
    review_inventory["properties"]["baseline_delta_root_sha256"] = _sha_schema(
        "INDEPENDENT_REVIEW_BASELINE_DELTA_SET",
        semantics="ORDERED_DELTA_SET_ROOT",
    )
    attestation = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_EXECUTION_PREFLIGHT_ATTESTATION_v2",
                "type": "string",
            },
            "source_commit": _commit_schema(),
            "source_tree": _commit_schema(),
            "reviewed_contract": _git_identity_schema("V2_CONTRACT"),
            "source_registry": _git_identity_schema("SOURCE_REGISTRY"),
            "schema_bundle": _identity_schema("V2_SCHEMA_BUNDLE"),
            "protocol_bundle": _git_identity_schema("EXECUTION_PROTOCOL"),
            "implementation_inventory": _identity_schema("AUTHORIZED_IMPLEMENTATION"),
            "consumer_inventory": _identity_schema("PREFLIGHT_CONSUMER_INVENTORY"),
            "consumer_identity_count": count,
            "consumer_identity_root_sha256": _sha_schema(
                "PREFLIGHT_CONSUMER_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "runtime_required_count": count,
            "runtime_required_identity_root_sha256": _sha_schema(
                "PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "nonruntime_count": count,
            "baseline_delta_root_sha256": _sha_schema(
                "BASELINE_DELTA_SET", semantics="ORDERED_DELTA_SET_ROOT"
            ),
            "candidate_supplied_inventory_used": {"const": False, "type": "boolean"},
        }
    )
    source = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_EXECUTION_SOURCE_MANIFEST_v3",
                "type": "string",
            },
            "source_commit": _commit_schema(),
            "accepted_contract_review": _git_identity_schema(
                "ACCEPTED_V2_INDEPENDENT_REVIEW"
            ),
            "reviewed_contract": _git_identity_schema("V2_CONTRACT"),
            "preflight_attestation": _identity_schema(
                "EXECUTION_PREFLIGHT_ATTESTATION"
            ),
            "source_registry": _git_identity_schema("SOURCE_REGISTRY"),
            "schema_bundle": _identity_schema("V2_SCHEMA_BUNDLE"),
            "protocol_bundle": _git_identity_schema("EXECUTION_PROTOCOL"),
            "implementation_inventory": _identity_schema("AUTHORIZED_IMPLEMENTATION"),
            "consumer_identity_count": count,
            "consumer_identity_root_sha256": _sha_schema(
                "PREFLIGHT_CONSUMER_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "runtime_required_count": count,
            "runtime_required_identity_root_sha256": _sha_schema(
                "PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "execution_command": {"minLength": 1, "type": "string"},
            "runtime_output_count": {"const": 0, "type": "integer"},
            "immutable": {"const": True, "type": "boolean"},
        }
    )
    candidate_map = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v4",
                "type": "string",
            },
            "source_manifest": _identity_schema("SOURCE_MANIFEST"),
            "preflight_inventory": _identity_schema("PREFLIGHT_CONSUMER_INVENTORY"),
            "inventory_origin": {
                "const": "EXACT_PREFLIGHT_REPOSITORY_PROJECTION",
                "type": "string",
            },
            "consumers": {"items": row, "type": "array", "uniqueItems": True},
            "consumer_identity_count": count,
            "consumer_identity_root_sha256": _sha_schema(
                "PREFLIGHT_CONSUMER_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "runtime_required_count": count,
            "runtime_required_identity_root_sha256": _sha_schema(
                "PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "nonruntime_count": count,
            "status": {
                "const": "EXACT_PREFLIGHT_INVENTORY_RECONCILIATION_REQUIRED",
                "type": "string",
            },
        }
    )
    trace_event = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_SHADOW_TRACE_EVENT_v4",
                "type": "string",
            },
            "run_id": {"minLength": 1, "type": "string"},
            "trace_id": {"pattern": "^lct2:[0-9a-f]{64}$", "type": "string"},
            "consumer_id": {"pattern": "^lcc2:[0-9a-f]{64}$", "type": "string"},
            "consumer_path": _path_schema(),
            "consumer_source_sha256": _sha_schema(
                "REPOSITORY_CONSUMER_SOURCE",
                semantics="MEMBER_CONTENT_SHA256",
                resolver="SIBLING_CONSUMER_ID",
            ),
            "operation_class": {"enum": OPERATION_CLASSES, "type": "string"},
            "candidate_result_sha256": _sha_schema(
                "CURRENT_PROJECTION_OPERATION_RESULT",
                semantics="MEMBER_CONTENT_SHA256",
                resolver="SIBLING_CONSUMER_ID",
            ),
            "legacy_result_sha256": _sha_schema(
                "SOURCE_REGISTRY_OPERATION_RESULT",
                semantics="MEMBER_CONTENT_SHA256",
                resolver="SIBLING_CONSUMER_ID",
            ),
            "semantic_parity": {"type": "boolean"},
            "write_attempted": {"type": "boolean"},
        }
    )
    trace_manifest = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v4",
                "type": "string",
            },
            "run_id": {"minLength": 1, "type": "string"},
            "source_manifest": _identity_schema("SOURCE_MANIFEST"),
            "preflight_inventory": _identity_schema("PREFLIGHT_CONSUMER_INVENTORY"),
            "consumer_map": _identity_schema("CONSUMER_MAP"),
            "runtime_trace": _identity_schema("RUNTIME_TRACE"),
            "traced_consumer_identity_root_sha256": _sha_schema(
                "PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "runtime_required_identity_root_sha256": _sha_schema(
                "PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "event_count": count,
            "runtime_required_count": count,
            "unmatched_trace_count": {"const": 0, "type": "integer"},
            "unobserved_runtime_required_count": {"const": 0, "type": "integer"},
            "status": {
                "enum": ["COMPLETE_PARITY", "B_BLOCKED_TRACE_EVIDENCE"],
                "type": "string",
            },
        }
    )
    trust_anchors = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v2",
                "type": "string",
            },
            "accepted_contract_review": _git_identity_schema(
                "ACCEPTED_V2_INDEPENDENT_REVIEW"
            ),
            "source_registry": _git_identity_schema("SOURCE_REGISTRY"),
            "schema_bundle": _identity_schema("V2_SCHEMA_BUNDLE"),
            "protocol_bundle": _git_identity_schema("EXECUTION_PROTOCOL"),
            "authority_commitment_sha256": _sha_schema(
                "SOURCE_AUTHORITY_COMMITMENT"
            ),
            "stage_b_authorized": {"const": False, "type": "boolean"},
        }
    )
    rollback = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v2",
                "type": "string",
            },
            "pre_run_inventory_sha256": _sha_schema(
                "PRE_RUN_INVENTORY_SET", semantics="ORDERED_PATH_SET_ROOT"
            ),
            "allowed_output_paths_sha256": _sha_schema(
                "ALLOWED_OUTPUT_PATH_SET", semantics="ORDERED_PATH_SET_ROOT"
            ),
            "future_artifact_content_hashes_present": {
                "const": False,
                "type": "boolean",
            },
        }
    )
    writer_probe = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_WRITER_PROBE_v2",
                "type": "string",
            },
            "source_registry_write_attempted": {"const": False, "type": "boolean"},
            "write_outside_run_root_count": {"const": 0, "type": "integer"},
            "passed": {"type": "boolean"},
        }
    )
    candidate_artifact_types = [
        "CUSTODY_PAYLOAD",
        "HISTORY_SHARD",
        "CONSUMER_MAP",
        "CUSTODY_MANIFEST",
        "LEGACY_RECONSTRUCTION",
        "HISTORY_INDEX",
        "CURRENT_PROJECTION",
        "RUNTIME_TRACE",
        "RUNTIME_TRACE_MANIFEST",
        "REVIEWED_TRUST_ANCHORS",
        "WRITER_PROBE",
        "ROLLBACK_INVENTORY",
        "CONTROL_EVIDENCE",
        "VALIDATION_REPORT",
    ]
    artifact_row = _closed(
        {
            "artifact_type": {
                "enum": candidate_artifact_types,
                "type": "string",
            },
            "path": _path_schema(),
            "sha256": _sha_schema(
                "DYNAMIC_CANDIDATE_ARTIFACT",
                semantics="MEMBER_CONTENT_SHA256",
                resolver="SIBLING_ARTIFACT_TYPE",
            ),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )
    runtime = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_RUNTIME_MANIFEST_v3",
                "type": "string",
            },
            "run_id": {"pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$", "type": "string"},
            "source_manifest": _identity_schema("SOURCE_MANIFEST"),
            "candidate_artifacts": {
                "allOf": [
                    {
                        "contains": {
                            "properties": {
                                "artifact_type": {
                                    "const": artifact_type,
                                    "type": "string",
                                }
                            },
                            "required": ["artifact_type"],
                            "type": "object",
                        },
                        "minContains": 1,
                    }
                    for artifact_type in candidate_artifact_types
                ],
                "items": artifact_row,
                "minItems": len(candidate_artifact_types),
                "type": "array",
                "uniqueItems": True,
                "x-toe-required-artifact-types": candidate_artifact_types,
            },
            "candidate_artifact_count": {"minimum": 1, "type": "integer"},
            "candidate_artifact_root_sha256": _sha_schema(
                "ALL_CANDIDATE_ARTIFACT_SET", semantics="ORDERED_ARTIFACT_SET_ROOT"
            ),
            "environment": _closed(
                {
                    "filesystem_encoding": {"minLength": 1, "type": "string"},
                    "platform": {"minLength": 1, "type": "string"},
                    "python_version": {"minLength": 1, "type": "string"},
                }
            ),
            "execution_command": {"minLength": 1, "type": "string"},
            "status": {
                "enum": ["CANDIDATE_COMPLETE", "B_BLOCKED_CANDIDATE_PRESERVED"],
                "type": "string",
            },
            "block_reason_codes": {
                "items": {"minLength": 1, "type": "string"},
                "type": "array",
                "uniqueItems": True,
            },
        }
    )
    control_row = _closed(
        {
            "control_id": {"minLength": 1, "type": "string"},
            "baseline_core_candidate_root_sha256": _sha_schema(
                "CORE_CANDIDATE_ARTIFACT_SET",
                semantics="ORDERED_ARTIFACT_SET_ROOT",
            ),
            "passed": {"type": "boolean"},
            "observed_error_codes": {
                "items": {"minLength": 1, "type": "string"},
                "type": "array",
                "uniqueItems": True,
            },
        }
    )
    control = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_CONTROL_EVIDENCE_v2",
                "type": "string",
            },
            "run_id": {"minLength": 1, "type": "string"},
            "control_results": {
                "items": control_row,
                "maxItems": 76,
                "minItems": 76,
                "type": "array",
            },
            "control_result_count": {"const": 76, "type": "integer"},
            "baseline_core_candidate_root_sha256": _sha_schema(
                "CORE_CANDIDATE_ARTIFACT_SET",
                semantics="ORDERED_ARTIFACT_SET_ROOT",
            ),
            "results_root_sha256": _sha_schema(
                "CONTROL_RESULT_SET", semantics="ORDERED_CONTROL_RESULT_ROOT"
            ),
            "all_results_passed": {"type": "boolean"},
            "status": {"enum": ["ALL_76_CONTROLS_PASSED", "B_BLOCKED"], "type": "string"},
        }
    )
    report = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_EXECUTION_REPORT_v3",
                "type": "string",
            },
            "run_id": {"minLength": 1, "type": "string"},
            "runtime_manifest": _identity_schema("RUNTIME_MANIFEST"),
            "control_evidence": _identity_schema("CONTROL_EVIDENCE"),
            "preflight_consumer_identity_root_sha256": _sha_schema(
                "PREFLIGHT_CONSUMER_IDENTITY_SET", semantics="ORDERED_IDENTITY_SET_ROOT"
            ),
            "candidate_consumer_identity_root_sha256": _sha_schema(
                "PREFLIGHT_CONSUMER_IDENTITY_SET", semantics="ORDERED_IDENTITY_SET_ROOT"
            ),
            "runtime_required_identity_root_sha256": _sha_schema(
                "PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET",
                semantics="ORDERED_IDENTITY_SET_ROOT",
            ),
            "validator_decisions": {
                "items": _closed(
                    {
                        "decision_id": {"minLength": 1, "type": "string"},
                        "passed": {"type": "boolean"},
                    }
                ),
                "minItems": 1,
                "type": "array",
            },
            "status": {
                "enum": ["STAGE_A_CANDIDATE_COMPLETE", "B_BLOCKED_CANDIDATE_PRESERVED"],
                "type": "string",
            },
            "block_reason_codes": {
                "items": {"minLength": 1, "type": "string"},
                "type": "array",
                "uniqueItems": True,
            },
        }
    )
    terminal = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_TERMINAL_ENVELOPE_v2",
                "type": "string",
            },
            "run_id": {"minLength": 1, "type": "string"},
            "source_manifest": _identity_schema("SOURCE_MANIFEST"),
            "runtime_manifest": _identity_schema("RUNTIME_MANIFEST"),
            "execution_report": _identity_schema("EXECUTION_REPORT"),
            "candidate_artifact_root_sha256": _sha_schema(
                "ALL_CANDIDATE_ARTIFACT_SET", semantics="ORDERED_ARTIFACT_SET_ROOT"
            ),
            "candidate_status": {
                "enum": [
                    "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW",
                    "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED",
                ],
                "type": "string",
            },
            "block_reason_codes": {
                "items": {"minLength": 1, "type": "string"},
                "type": "array",
                "uniqueItems": True,
            },
            "terminal": {"const": True, "type": "boolean"},
        }
    )
    review = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_INDEPENDENT_REVIEW_BINDING_v2",
                "type": "string",
            },
            "terminal_envelope": _identity_schema("TERMINAL_ENVELOPE"),
            "review_inventory": _identity_schema(
                "INDEPENDENT_REVIEW_CONSUMER_INVENTORY"
            ),
            "execution_inventory_root_sha256": _sha_schema(
                "PREFLIGHT_CONSUMER_IDENTITY_SET", semantics="ORDERED_IDENTITY_SET_ROOT"
            ),
            "independent_rescan_root_sha256": _sha_schema(
                "INDEPENDENT_REVIEW_IDENTITY_SET", semantics="ORDERED_IDENTITY_SET_ROOT"
            ),
            "independent_rescan_performed": {"const": True, "type": "boolean"},
            "inventory_source": {"const": "INDEPENDENT_GIT_OBJECT_RESCAN", "type": "string"},
            "decision": {"enum": ["ACCEPT_STAGE_A_CANDIDATE_ONLY", "B_BLOCKED"], "type": "string"},
            "stage_b_authorized": {"const": False, "type": "boolean"},
        }
    )
    diagnostic = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_PREFLIGHT_DIAGNOSTIC_v2",
                "type": "string",
            },
            "classification": {
                "enum": [
                    "blocked_preflight_source_registry_mismatch",
                    "blocked_preflight_consumer_rescan_failure",
                    "blocked_preflight_hash_graph_invalid",
                    "blocked_preflight_schema_edge_coverage_failure",
                ],
                "type": "string",
            },
            "error_code": {"maxLength": 96, "minLength": 1, "type": "string"},
            "message": {"maxLength": 512, "minLength": 1, "type": "string"},
            "exit_code": {"minimum": 1, "type": "integer"},
            "candidate_set_created": {"const": False, "type": "boolean"},
            "prototype_run_root_created": {"const": False, "type": "boolean"},
            "controls_observed": {"const": 0, "type": "integer"},
        }
    )
    schemas = {
        "preflight_consumer_inventory": inventory,
        "independent_review_consumer_inventory": review_inventory,
        "execution_preflight_attestation": attestation,
        "execution_source_manifest": source,
        "candidate_consumer_map": candidate_map,
        "runtime_trace_event": trace_event,
        "runtime_trace_manifest": trace_manifest,
        "reviewed_trust_anchors": trust_anchors,
        "rollback_inventory": rollback,
        "writer_probe": writer_probe,
        "control_evidence": control,
        "runtime_manifest": runtime,
        "execution_report": report,
        "terminal_envelope": terminal,
        "independent_review_binding": review,
        "preflight_diagnostic": diagnostic,
    }
    for name, schema in schemas.items():
        schema["$id"] = f"https://toe.local/schema/registry-stage-a-v2/{name}.json"
        schema["$schema"] = draft
        Draft202012Validator.check_schema(schema)
    return schemas


INHERITED_SCHEMA_ARTIFACT_TYPES: Final = {
    "compatibility_reconstruction_result": "LEGACY_RECONSTRUCTION",
    "current_projection": "CURRENT_PROJECTION",
    "history_index": "HISTORY_INDEX",
    "history_shard_record": "HISTORY_SHARD",
    "legacy_byte_custody_manifest": "CUSTODY_MANIFEST",
    "validation_report": "VALIDATION_REPORT",
}

CUSTOM_SCHEMA_ARTIFACT_TYPES: Final = {
    "preflight_consumer_inventory": "PREFLIGHT_CONSUMER_INVENTORY",
    "independent_review_consumer_inventory": (
        "INDEPENDENT_REVIEW_CONSUMER_INVENTORY"
    ),
    "execution_preflight_attestation": "EXECUTION_PREFLIGHT_ATTESTATION",
    "execution_source_manifest": "SOURCE_MANIFEST",
    "candidate_consumer_map": "CONSUMER_MAP",
    "runtime_trace_event": "RUNTIME_TRACE",
    "runtime_trace_manifest": "RUNTIME_TRACE_MANIFEST",
    "reviewed_trust_anchors": "REVIEWED_TRUST_ANCHORS",
    "rollback_inventory": "ROLLBACK_INVENTORY",
    "writer_probe": "WRITER_PROBE",
    "control_evidence": "CONTROL_EVIDENCE",
    "runtime_manifest": "RUNTIME_MANIFEST",
    "execution_report": "EXECUTION_REPORT",
    "terminal_envelope": "TERMINAL_ENVELOPE",
    "independent_review_binding": "INDEPENDENT_REVIEW",
    "preflight_diagnostic": "PREFLIGHT_DIAGNOSTIC",
}


def _inherited_hash_target(artifact_type: str, path: str) -> tuple[str, str]:
    """Return the reviewed target and semantics for an inherited hash leaf."""

    if artifact_type == "LEGACY_RECONSTRUCTION":
        if path.endswith("/custody_payload_identity/sha256"):
            return "CUSTODY_PAYLOAD", "CONTENT_SHA256"
        if path.endswith("/reconstruction_identity/sha256"):
            return "LEGACY_RECONSTRUCTED_BYTES", "CONTENT_SHA256"
        if path.endswith("/source_identity/sha256"):
            return "SOURCE_REGISTRY", "CONTENT_SHA256"
        if path.endswith("/validator_identity/sha256"):
            return "AUTHORIZED_IMPLEMENTATION", "CONTENT_SHA256"
    elif artifact_type == "CURRENT_PROJECTION":
        if path.endswith("/history_index_pointer/sha256"):
            return "HISTORY_INDEX", "CONTENT_SHA256"
        if path.endswith("/source_legacy_identity/sha256"):
            return "SOURCE_REGISTRY", "CONTENT_SHA256"
        if path.endswith("/maintenance_authority/evidence/sha256"):
            return "AUTHORITY_EVIDENCE", "CONTENT_SHA256"
        if path.endswith("/scientific_authority/authority_commitment_sha256"):
            return "SOURCE_AUTHORITY_COMMITMENT", "CONTENT_SHA256"
        if "/current_artifacts/*/sha256" in path:
            return "SOURCE_CURRENT_ARTIFACT", "CONTENT_SHA256"
    elif artifact_type == "HISTORY_INDEX":
        if path.endswith("/consumer_source_map_pointer/sha256"):
            return "CONSUMER_MAP", "CONTENT_SHA256"
        if path.endswith("/custody_manifest_pointer/sha256"):
            return "CUSTODY_MANIFEST", "CONTENT_SHA256"
        if path.endswith("/source_registry_identity/sha256"):
            return "SOURCE_REGISTRY", "CONTENT_SHA256"
        if path.endswith("/shards/*/sha256"):
            return "HISTORY_SHARD", "CONTENT_SHA256"
        if path.endswith("/shards/*/record_id_root_sha256"):
            return "HISTORY_SHARD_RECORD_ID_SET", "ORDERED_RECORD_SET_ROOT"
        if path.endswith("/record_accounting/authority_commitment_sha256"):
            return "SOURCE_AUTHORITY_COMMITMENT", "CONTENT_SHA256"
        if path.endswith(
            "/record_accounting/full_record_identity_root_sha256"
        ):
            return "HISTORY_FULL_RECORD_IDENTITY_SET", "ORDERED_RECORD_SET_ROOT"
        if path.endswith(
            "/record_accounting/identity_payload_pointer_root_sha256"
        ):
            return (
                "HISTORY_IDENTITY_PAYLOAD_POINTER_SET",
                "ORDERED_RECORD_SET_ROOT",
            )
        if path.endswith("/record_accounting/original_pointer_set_sha256"):
            return "HISTORY_ORIGINAL_POINTER_SET", "ORDERED_RECORD_SET_ROOT"
    elif artifact_type == "HISTORY_SHARD":
        if path.endswith("/payload_sha256"):
            return "SOURCE_REGISTRY_RECORD_PAYLOAD", "CONTENT_SHA256"
    elif artifact_type == "CUSTODY_MANIFEST":
        if path.endswith("/contract_pointer/sha256"):
            return "CUSTODY_CONTRACT", "CONTENT_SHA256"
        if path.endswith("/external_binding/accepted_guardrail_packet_sha256"):
            return "GUARDRAIL_PACKET", "CONTENT_SHA256"
        if path.endswith("/external_binding/accepted_guardrail_review_sha256"):
            return "GUARDRAIL_REVIEW", "CONTENT_SHA256"
        if path.endswith("/generation_provenance/generator_sha256"):
            return "AUTHORIZED_IMPLEMENTATION", "CONTENT_SHA256"
        if path.endswith("/payload_identity/compressed_sha256"):
            return "CUSTODY_PAYLOAD", "CONTENT_SHA256"
        if path.endswith("/reconstruction_requirement/decompressed_sha256"):
            return "SOURCE_REGISTRY", "CONTENT_SHA256"
        if path.endswith("/source_identity/sha256"):
            return "SOURCE_REGISTRY", "CONTENT_SHA256"
    elif artifact_type == "VALIDATION_REPORT":
        if path.endswith("/candidate_root_sha256"):
            return "CORE_CANDIDATE_ARTIFACT_SET", "ORDERED_ARTIFACT_SET_ROOT"
        if path.endswith("/profile_control_root_sha256"):
            return "CONTROL_PROFILE", "ORDERED_CONTROL_PROFILE_ROOT"
        if path.endswith("/trust_anchor_sha256"):
            return "REVIEWED_TRUST_ANCHORS", "CONTENT_SHA256"
    raise V2PreparationError(
        f"unreviewed inherited hash field: {artifact_type}{path}"
    )


def _annotate_inherited_schema(
    schema: dict[str, Any], artifact_type: str
) -> dict[str, Any]:
    output = deepcopy(schema)

    def walk(value: Any, path: str) -> None:
        if not isinstance(value, dict):
            return
        properties = value.get("properties")
        if isinstance(properties, dict):
            for name, child in properties.items():
                child_path = f"{path}/{name}"
                if _is_hash_bearing_schema_field(name, child):
                    target, semantics = _inherited_hash_target(
                        artifact_type, child_path
                    )
                    resolver = "FIXED_ARTIFACT_TYPE"
                    if (
                        artifact_type == "HISTORY_SHARD"
                        and child_path.endswith("/payload_sha256")
                    ):
                        semantics = "MEMBER_CONTENT_SHA256"
                        resolver = "SIBLING_RECORD_ID"
                    elif (
                        artifact_type == "CURRENT_PROJECTION"
                        and "/current_artifacts/*/sha256" in child_path
                    ):
                        semantics = "MEMBER_CONTENT_SHA256"
                        resolver = "SIBLING_PATH"
                    elif (
                        artifact_type == "HISTORY_INDEX"
                        and "/shards/*/" in child_path
                    ):
                        resolver = "SIBLING_SHARD_PATH"
                        if child_path.endswith("/sha256"):
                            semantics = "MEMBER_CONTENT_SHA256"
                    child["x-toe-hash-edge"] = {
                        "hash_semantics": semantics,
                        "referenced_artifact_type": target,
                        "target_resolver": resolver,
                    }
                walk(child, child_path)
        if isinstance(value.get("items"), dict):
            walk(value["items"], f"{path}/*")
        for keyword in ("prefixItems", "oneOf", "allOf", "anyOf"):
            alternatives = value.get(keyword)
            if isinstance(alternatives, list):
                for child in alternatives:
                    walk(child, path)

    walk(output, "")
    Draft202012Validator.check_schema(output)
    return output


_RUNTIME_SCHEMA_CACHE: dict[str, dict[str, Any]] | None = None


def build_runtime_schemas() -> dict[str, dict[str, Any]]:
    global _RUNTIME_SCHEMA_CACHE
    if _RUNTIME_SCHEMA_CACHE is not None:
        return deepcopy(_RUNTIME_SCHEMA_CACHE)
    bundle = _strict_json(_git_blob(SOURCE_COMMIT, V3_SCHEMAS_REL))
    inherited = {
        name: _annotate_inherited_schema(
            bundle["schemas"][name], INHERITED_SCHEMA_ARTIFACT_TYPES[name]
        )
        for name in INHERITED_SCHEMA_ARTIFACT_TYPES
    }
    schemas = {**inherited, **_custom_runtime_schemas()}
    if set(schemas) != (
        set(INHERITED_SCHEMA_ARTIFACT_TYPES) | set(CUSTOM_SCHEMA_ARTIFACT_TYPES)
    ):
        raise V2PreparationError("runtime schema catalog differs")
    _RUNTIME_SCHEMA_CACHE = deepcopy(schemas)
    return schemas


def _schema_artifact_type(schema_name: str) -> str:
    if schema_name in INHERITED_SCHEMA_ARTIFACT_TYPES:
        return INHERITED_SCHEMA_ARTIFACT_TYPES[schema_name]
    return CUSTOM_SCHEMA_ARTIFACT_TYPES[schema_name]


def _escape_pointer(token: str) -> str:
    return token.replace("~", "~0").replace("/", "~1")


def _schema_hash_fields(schema: dict[str, Any]) -> list[dict[str, Any]]:
    """Independently enumerate normalized SHA-256 instance fields."""

    observed: dict[tuple[str, str, str, str], dict[str, Any]] = {}

    def walk(value: Any, path: str, required: bool) -> None:
        if not isinstance(value, dict):
            return
        properties = value.get("properties")
        required_names = set(value.get("required", []))
        if isinstance(properties, dict):
            for name, child in properties.items():
                child_path = f"{path}/{_escape_pointer(name)}"
                child_required = required and name in required_names
                if _is_hash_bearing_schema_field(name, child):
                    annotation = child.get("x-toe-hash-edge")
                    if not isinstance(annotation, dict):
                        raise V2PreparationError(
                            f"V2-E-HASH-FIELD-UNDECLARED:{child_path}"
                        )
                    key = (
                        child_path,
                        annotation["referenced_artifact_type"],
                        annotation["hash_semantics"],
                        annotation["target_resolver"],
                    )
                    observed[key] = {
                        "schema_field_path": child_path,
                        **annotation,
                        "required_optional_status": (
                            "REQUIRED" if child_required else "CONDITIONAL_OR_OPTIONAL"
                        ),
                    }
                walk(child, child_path, child_required)
        if isinstance(value.get("items"), dict):
            walk(
                value["items"],
                f"{path}/*",
                required and value.get("minItems", 0) > 0,
            )
        prefix = value.get("prefixItems")
        if isinstance(prefix, list):
            for child in prefix:
                walk(child, f"{path}/*", required)
        for keyword in ("oneOf", "allOf", "anyOf"):
            alternatives = value.get(keyword)
            if isinstance(alternatives, list):
                for child in alternatives:
                    walk(child, path, required)

    walk(schema, "", True)
    return [observed[key] for key in sorted(observed)]


def derive_reviewed_edge_table(
    schemas: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    candidate_array = schemas["runtime_manifest"]["properties"][
        "candidate_artifacts"
    ]
    required_dynamic_targets = {
        constraint["contains"]["properties"]["artifact_type"]["const"]
        for constraint in candidate_array.get("allOf", [])
        if constraint.get("minContains", 1) > 0
        and isinstance(constraint.get("contains"), dict)
        and isinstance(
            constraint["contains"].get("properties", {}).get(
                "artifact_type"
            ),
            dict,
        )
        and isinstance(
            constraint["contains"]["properties"]["artifact_type"].get(
                "const"
            ),
            str,
        )
    }
    declared_required_dynamic_targets = set(
        candidate_array.get("x-toe-required-artifact-types", [])
    )
    if required_dynamic_targets != declared_required_dynamic_targets:
        raise V2PreparationError("V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH")
    rows: list[dict[str, Any]] = []
    for schema_name in sorted(schemas):
        artifact = _schema_artifact_type(schema_name)
        if artifact == "PREFLIGHT_DIAGNOSTIC":
            continue
        containing_phase, containing_ordinal, _ = ARTIFACT_PHASES[artifact]
        for field in _schema_hash_fields(schemas[schema_name]):
            declared_target = field["referenced_artifact_type"]
            targets = [declared_target]
            if declared_target == "DYNAMIC_CANDIDATE_ARTIFACT":
                targets = list(
                    schemas["runtime_manifest"]["properties"]
                    ["candidate_artifacts"]["items"]["properties"]
                    ["artifact_type"]["enum"]
                )
            for target in targets:
                target_phase, target_ordinal, _ = ARTIFACT_PHASES[target]
                branches = ARTIFACT_BRANCHES.get(
                    artifact, ("COMPLETE", "POST_GENERATION_BLOCKED")
                )
                target_required = (
                    field["required_optional_status"] == "REQUIRED"
                    and (
                        declared_target != "DYNAMIC_CANDIDATE_ARTIFACT"
                        or target in required_dynamic_targets
                    )
                )
                applicability = (
                    "REQUIRED"
                    if target_required
                    else "CONDITIONAL_OR_OPTIONAL"
                )
                rows.append(
                    {
                        "blocked_path_applicability": (
                            applicability
                            if "POST_GENERATION_BLOCKED" in branches
                            else "INAPPLICABLE"
                        ),
                        "complete_path_applicability": (
                            applicability
                            if "COMPLETE" in branches
                            else "INAPPLICABLE"
                        ),
                        "containing_artifact_type": artifact,
                        "containing_generation_ordinal": containing_ordinal,
                        "containing_generation_phase": containing_phase,
                        "containing_schema_id": schemas[schema_name]["$id"],
                        "hash_semantics": field["hash_semantics"],
                        "referenced_artifact_type": target,
                        "referenced_generation_ordinal": target_ordinal,
                        "referenced_generation_phase": target_phase,
                        "required_optional_status": (
                            "REQUIRED"
                            if target_required
                            else "CONDITIONAL_OR_OPTIONAL"
                        ),
                        "schema_field_path": field["schema_field_path"],
                        "target_resolver": (
                            f"SIBLING_ARTIFACT_TYPE={target}"
                            if declared_target
                            == "DYNAMIC_CANDIDATE_ARTIFACT"
                            else field["target_resolver"]
                        ),
                    }
                )
    return sorted(
        rows,
        key=lambda row: (
            row["containing_generation_ordinal"],
            row["containing_artifact_type"],
            row["schema_field_path"],
            row["referenced_artifact_type"],
        ),
    )


def _topological_sort(graph: dict[str, set[str]]) -> list[str]:
    remaining = {node: set(dependencies) for node, dependencies in graph.items()}
    output: list[str] = []
    while remaining:
        ready = sorted(node for node, deps in remaining.items() if not deps)
        if not ready:
            raise V2PreparationError("V2-E-SCHEMA-GENERATION-ORDER-MISMATCH")
        for node in ready:
            output.append(node)
            remaining.pop(node)
            for dependencies in remaining.values():
                dependencies.discard(node)
    return output


def validate_schema_derived_graph(
    schemas: dict[str, dict[str, Any]],
    edge_table: list[dict[str, Any]],
    *,
    declared_edge_table: list[dict[str, Any]] | None = None,
) -> list[str]:
    actual = derive_reviewed_edge_table(schemas)
    if actual != edge_table:
        raise V2PreparationError("V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH")
    if declared_edge_table is not None and declared_edge_table != actual:
        raise V2PreparationError("V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH")
    graph: dict[str, set[str]] = {
        artifact: set()
        for artifact, (_, _, kind) in ARTIFACT_PHASES.items()
        if kind != "EXTERNAL"
    }
    for row in actual:
        source = row["containing_artifact_type"]
        target = row["referenced_artifact_type"]
        if source == target:
            raise V2PreparationError("V2-E-SCHEMA-GENERATION-ORDER-MISMATCH")
        if (
            row["referenced_generation_ordinal"]
            >= row["containing_generation_ordinal"]
        ):
            raise V2PreparationError("V2-E-LATER-PHASE-REFERENCE")
        if source in graph and target in graph:
            graph[source].add(target)
    for source, targets in graph.items():
        for target in targets:
            if source in graph.get(target, set()):
                raise V2PreparationError("V2-E-SCHEMA-GENERATION-ORDER-MISMATCH")
    order = _topological_sort(graph)
    if len(order) != len(graph) or len(order) != len(set(order)):
        raise V2PreparationError("V2-E-SCHEMA-GENERATION-ORDER-MISMATCH")
    return order


def build_artifact_schemas() -> dict[str, dict[str, Any]]:
    """Public name emphasizing that the schemas, not prose, define the graph."""

    return build_runtime_schemas()


def derive_schema_edges(
    schemas: dict[str, dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    return derive_reviewed_edge_table(
        build_runtime_schemas() if schemas is None else schemas
    )


RUNTIME_SCHEMA_COUNT: Final = len(build_runtime_schemas())
REVIEWED_EDGE_TABLE: Final = derive_schema_edges()


def validate_schema_graph(
    schemas: dict[str, dict[str, Any]] | None = None,
    edge_table: list[dict[str, Any]] | None = None,
    artifact_phases: dict[str, tuple[str, int, str]] | None = None,
    *,
    declared_edge_table: list[dict[str, Any]] | None = None,
    generation_order: list[str] | None = None,
) -> list[str]:
    """Validate schema/table/order agreement with stable fault-specific codes."""

    schemas = build_runtime_schemas() if schemas is None else schemas
    supplied = REVIEWED_EDGE_TABLE if edge_table is None else edge_table
    phases = ARTIFACT_PHASES if artifact_phases is None else artifact_phases
    actual = derive_schema_edges(schemas)

    for row in supplied:
        source = row["containing_artifact_type"]
        target = row["referenced_artifact_type"]
        if source == target:
            raise V2PreparationError("V2-E-HASH-GRAPH-SELF-EDGE")
        if any(
            other["containing_artifact_type"] == target
            and other["referenced_artifact_type"] == source
            for other in supplied
        ):
            raise V2PreparationError("V2-E-HASH-GRAPH-RECIPROCAL-EDGE")

    actual_keys = {
        (
            row["containing_artifact_type"],
            row["schema_field_path"],
            row["referenced_artifact_type"],
        ): row
        for row in actual
    }
    supplied_keys = {
        (
            row["containing_artifact_type"],
            row["schema_field_path"],
            row["referenced_artifact_type"],
        ): row
        for row in supplied
    }
    if set(actual_keys) - set(supplied_keys):
        raise V2PreparationError("V2-E-HASH-FIELD-UNDECLARED")
    if supplied != actual:
        raise V2PreparationError("V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH")
    if declared_edge_table is not None and declared_edge_table != actual:
        raise V2PreparationError("V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH")

    phase_rows: dict[str, tuple[str, int, str]] = {}
    for artifact, value in phases.items():
        if isinstance(value, tuple):
            phase_rows[artifact] = value
        elif isinstance(value, dict):
            phase_rows[artifact] = (
                str(value.get("generation_phase", value.get("phase"))),
                int(value.get("ordinal", value.get("order"))),
                str(value.get("kind", "ARTIFACT")),
            )
        else:
            raise V2PreparationError("V2-E-REQUIRED-NODE-CARDINALITY")
    if len(phase_rows) != len(phases):
        raise V2PreparationError("V2-E-REQUIRED-NODE-CARDINALITY")

    graph: dict[str, set[str]] = {
        artifact: set()
        for artifact, (_, _, kind) in phase_rows.items()
        if kind != "EXTERNAL"
    }
    for row in actual:
        source = row["containing_artifact_type"]
        target = row["referenced_artifact_type"]
        if source not in phase_rows:
            raise V2PreparationError("V2-E-REQUIRED-NODE-CARDINALITY")
        if target == "DYNAMIC_CANDIDATE_ARTIFACT":
            target_ordinal = 50
        elif target not in phase_rows:
            raise V2PreparationError("V2-E-REQUIRED-NODE-CARDINALITY")
        else:
            target_ordinal = phase_rows[target][1]
        if target_ordinal >= phase_rows[source][1]:
            code = (
                "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH"
                if artifact_phases is not None
                else "V2-E-LATER-PHASE-REFERENCE"
            )
            raise V2PreparationError(code)
        if source in graph and target in graph:
            graph[source].add(target)
    order = _topological_sort(graph)
    reviewed_order = [
        artifact
        for artifact, (_, _, kind) in sorted(
            phase_rows.items(), key=lambda item: (item[1][1], item[0])
        )
        if kind != "EXTERNAL"
    ]
    if generation_order is not None and generation_order != reviewed_order:
        raise V2PreparationError("V2-E-SCHEMA-GENERATION-ORDER-MISMATCH")
    positions = {artifact: index for index, artifact in enumerate(reviewed_order)}
    for source, targets in graph.items():
        for target in targets:
            if positions[target] >= positions[source]:
                raise V2PreparationError("V2-E-SCHEMA-GENERATION-ORDER-MISMATCH")
    return order


LEGACY_DAG_CONTROLS: Final = list(v1.SUCCESSOR_NEGATIVE_CONTROLS)
V2_NEGATIVE_CONTROLS: Final = [
    ("V2-NC-001", "declared_graph_differs_from_schema_graph", "V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH"),
    ("V2-NC-002", "schema_graph_differs_from_generation_order", "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH"),
    ("V2-NC-003", "undeclared_hash_bearing_field", "V2-E-HASH-FIELD-UNDECLARED"),
    ("V2-NC-004", "later_phase_artifact_required_too_early", "V2-E-LATER-PHASE-REFERENCE"),
    ("V2-NC-005", "consumer_map_truncated_to_one_row", "V2-E-CONSUMER-INVENTORY-INCOMPLETE"),
    ("V2-NC-006", "trace_truncated_to_match_consumer_map", "V2-E-RUNTIME-TRACE-INCOMPLETE"),
    ("V2-NC-007", "consumer_map_and_trace_locally_rebound", "V2-E-CONSUMER-LOCAL-REBIND"),
    ("V2-NC-008", "stale_historical_count_treated_as_current_truth", "V2-E-STALE-CONSUMER-COUNT"),
    ("V2-NC-009", "fresh_consumer_omitted", "V2-E-FRESH-CONSUMER-OMITTED"),
    ("V2-NC-010", "invented_consumer_inserted", "V2-E-CONSUMER-INVENTED"),
    ("V2-NC-011", "runtime_required_consumer_classified_nonruntime", "V2-E-RUNTIME-REQUIRED-MISCLASSIFIED"),
    ("V2-NC-012", "baseline_path_changed_without_delta_classification", "V2-E-BASELINE-CHANGE-UNCLASSIFIED"),
    ("V2-NC-013", "preflight_inventory_altered_after_source_manifest_creation", "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH"),
    ("V2-NC-014", "consumer_inventory_derived_from_candidate", "V2-E-CONSUMER-INVENTORY-TRUST-ROOT"),
    ("V2-NC-015", "review_trusts_execution_inventory_without_rescan", "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"),
]


def _summary_consumer_id(row: dict[str, Any]) -> str:
    identity = {
        "consumer_category": row["consumer_category"],
        "discovery_mechanism": row["discovery_mechanism"],
        "domain": "LOOP_CONTROL_CONSUMER_CALLSITE_ID_v2",
        "operation_class": row["operation_class"],
        "path": row["path"],
        "statement_or_callsite_sha256": row["statement_or_callsite_sha256"],
    }
    return "lcc2:" + sha256(compact_json_bytes(identity))


def _fixture_consumers() -> list[dict[str, Any]]:
    rows = [
        {
            "consumer_category": "DIRECT_READER",
            "discovery_mechanism": "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE",
            "operation_class": "READ_CURRENT_AUTHORITY",
            "path": "formal/python/tools/v2_fixture_reader.py",
            "runtime_required": True,
            "statement_or_callsite_sha256": "1" * 64,
        },
        {
            "consumer_category": "DOCUMENTATION_ONLY",
            "discovery_mechanism": "STRUCTURED_DOCUMENT_REFERENCE",
            "operation_class": "LITERAL_REFERENCE_ONLY",
            "path": "formal/docs/v2_fixture_reference.md",
            "runtime_required": False,
            "statement_or_callsite_sha256": "2" * 64,
        },
        {
            "consumer_category": "WRITER",
            "discovery_mechanism": "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE",
            "operation_class": "MUTATE_REGISTRY",
            "path": "formal/python/tools/v2_fixture_writer.py",
            "runtime_required": True,
            "statement_or_callsite_sha256": "3" * 64,
        },
    ]
    for row in rows:
        row["consumer_id"] = _summary_consumer_id(row)
    return rows


def _reviewed_generation_order() -> list[str]:
    return [
        artifact
        for artifact, (_, _, kind) in sorted(
            ARTIFACT_PHASES.items(), key=lambda item: (item[1][1], item[0])
        )
        if kind != "EXTERNAL"
    ]


def _draft_positive_lifecycle_fixture(branch: str) -> dict[str, Any]:
    if branch not in {"COMPLETE", "CANDIDATE_BLOCKED", "PREFLIGHT_BLOCKED"}:
        raise ValueError(f"unknown lifecycle branch: {branch}")
    common = {
        "artifact_phases": deepcopy(ARTIFACT_PHASES),
        "branch": branch,
        "declared_edge_table": deepcopy(REVIEWED_EDGE_TABLE),
        "generation_order": _reviewed_generation_order(),
        "legacy_fixture": v1.positive_successor_fixture(),
        "reviewed_edge_table": deepcopy(REVIEWED_EDGE_TABLE),
        "schemas": build_runtime_schemas(),
        "stage_a_authorized": False,
        "stage_b_authorized": False,
    }
    if branch == "PREFLIGHT_BLOCKED":
        return {
            **common,
            "bounded_diagnostic_only": True,
            "candidate_artifacts": [],
            "decision": "B_BLOCKED_PREFLIGHT",
            "execution_report_created": False,
            "exit_code": 2,
            "prototype_run_root_created": False,
            "runtime_manifest_created": False,
            "source_manifest_created": False,
            "terminal_envelope_created": False,
        }
    rows = _fixture_consumers()
    runtime_ids = [row["consumer_id"] for row in rows if row["runtime_required"]]
    preflight_sha = sha256(compact_json_bytes(rows))
    return {
        **common,
        "baseline_changed_paths": [rows[0]["path"]],
        "baseline_delta_changed_paths": [rows[0]["path"]],
        "bounded_diagnostic_only": False,
        "candidate_artifacts": [
            "CURRENT_PROJECTION",
            "HISTORY_INDEX",
            "HISTORY_SHARD",
            "CUSTODY_PAYLOAD",
            "CONSUMER_MAP",
            "RUNTIME_TRACE",
            "LEGACY_RECONSTRUCTION",
            "CONTROL_EVIDENCE",
        ],
        "candidate_consumer_rows": deepcopy(rows),
        "candidate_evidence_preserved": branch == "CANDIDATE_BLOCKED",
        "candidate_expected_consumer_count": None,
        "candidate_inventory_origin": "EXACT_PREFLIGHT_REPOSITORY_PROJECTION",
        "candidate_local_rebound": False,
        "decision": (
            "STAGE_A_CANDIDATE_COMPLETE_PENDING_REVIEW"
            if branch == "COMPLETE"
            else "B_BLOCKED"
        ),
        "execution_report_created": True,
        "preflight_consumer_rows": deepcopy(rows),
        "preflight_inventory_origin": "REPOSITORY_GIT_OBJECT_SCAN",
        "preflight_sha256": preflight_sha,
        "prototype_run_root_created": True,
        "review_acceptance": (
            "PENDING_INDEPENDENT_REVIEW" if branch == "COMPLETE" else "NOT_ACCEPTED"
        ),
        "review_consumer_ids": [row["consumer_id"] for row in rows],
        "review_inventory_origin": "INDEPENDENT_REVIEW_GIT_OBJECT_RESCAN",
        "review_runtime_required_ids": list(runtime_ids),
        "runtime_manifest_created": True,
        "runtime_trace_consumer_ids": list(runtime_ids),
        "source_manifest_created": True,
        "source_manifest_preflight_sha256": preflight_sha,
        "terminal_envelope_created": True,
    }


def _draft_validate_lifecycle_fixture(fixture: dict[str, Any], branch: str) -> None:
    if fixture.get("branch") != branch:
        raise V2PreparationError("V2-E-LIFECYCLE-BRANCH-MISMATCH")
    legacy_code = v1.validate_successor_fixture(fixture["legacy_fixture"])
    if legacy_code is not None:
        raise V2PreparationError(legacy_code)
    validate_schema_graph(
        fixture["schemas"],
        fixture["reviewed_edge_table"],
        fixture.get("artifact_phases"),
        declared_edge_table=fixture["declared_edge_table"],
        generation_order=fixture["generation_order"],
    )
    if branch == "PREFLIGHT_BLOCKED":
        if not (
            fixture["bounded_diagnostic_only"]
            and fixture["exit_code"] != 0
            and not fixture["prototype_run_root_created"]
            and not fixture["candidate_artifacts"]
            and not fixture["source_manifest_created"]
            and not fixture["runtime_manifest_created"]
            and not fixture["execution_report_created"]
            and not fixture["terminal_envelope_created"]
        ):
            raise V2PreparationError("V2-E-PREFLIGHT-BRANCH-UNSATISFIABLE")
        return
    if fixture["candidate_local_rebound"]:
        raise V2PreparationError("V2-E-CONSUMER-LOCAL-REBIND")
    if fixture["candidate_expected_consumer_count"] is not None:
        raise V2PreparationError("V2-E-STALE-CONSUMER-COUNT")
    if fixture["preflight_inventory_origin"] != "REPOSITORY_GIT_OBJECT_SCAN":
        raise V2PreparationError("V2-E-CONSUMER-INVENTORY-TRUST-ROOT")
    if fixture["candidate_inventory_origin"] != "EXACT_PREFLIGHT_REPOSITORY_PROJECTION":
        raise V2PreparationError("V2-E-CONSUMER-INVENTORY-TRUST-ROOT")
    if fixture["preflight_sha256"] != fixture["source_manifest_preflight_sha256"]:
        raise V2PreparationError("V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH")
    if set(fixture["baseline_changed_paths"]) - set(fixture["baseline_delta_changed_paths"]):
        raise V2PreparationError("V2-E-BASELINE-CHANGE-UNCLASSIFIED")

    preflight = {row["consumer_id"]: row for row in fixture["preflight_consumer_rows"]}
    candidate_rows = fixture["candidate_consumer_rows"]
    candidate_ids = [row["consumer_id"] for row in candidate_rows]
    if len(candidate_ids) != len(set(candidate_ids)):
        raise V2PreparationError("V2-E-DUPLICATE-CONSUMER-ID")
    candidate = {row["consumer_id"]: row for row in candidate_rows}
    for consumer_id in set(preflight) & set(candidate):
        if preflight[consumer_id]["runtime_required"] != candidate[consumer_id]["runtime_required"]:
            raise V2PreparationError("V2-E-RUNTIME-REQUIRED-MISCLASSIFIED")
    omitted = set(preflight) - set(candidate)
    invented = set(candidate) - set(preflight)
    if omitted and len(candidate) == 1:
        raise V2PreparationError("V2-E-CONSUMER-INVENTORY-INCOMPLETE")
    if omitted:
        raise V2PreparationError("V2-E-FRESH-CONSUMER-OMITTED")
    if invented:
        raise V2PreparationError("V2-E-CONSUMER-INVENTED")
    runtime_required = {
        consumer_id
        for consumer_id, row in preflight.items()
        if row["runtime_required"]
    }
    traces = fixture["runtime_trace_consumer_ids"]
    if len(traces) != len(set(traces)) or set(traces) != runtime_required:
        raise V2PreparationError("V2-E-RUNTIME-TRACE-INCOMPLETE")
    if fixture["review_inventory_origin"] != "INDEPENDENT_REVIEW_GIT_OBJECT_RESCAN":
        raise V2PreparationError("V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED")
    if set(fixture["review_consumer_ids"]) != set(preflight) or set(
        fixture["review_runtime_required_ids"]
    ) != runtime_required:
        raise V2PreparationError("V2-E-REVIEW-CONSUMER-RESCAN-MISMATCH")
    if not all(
        fixture[key]
        for key in (
            "source_manifest_created",
            "runtime_manifest_created",
            "execution_report_created",
            "terminal_envelope_created",
        )
    ):
        raise V2PreparationError("V2-E-POST-GENERATION-BLOCKED-CHAIN-UNSATISFIABLE")
    if branch == "CANDIDATE_BLOCKED" and not fixture["candidate_evidence_preserved"]:
        raise V2PreparationError("V2-E-BLOCKED-CANDIDATE-EVIDENCE-NOT-PRESERVED")


def _draft_mutate_lifecycle_fixture(fixture: dict[str, Any], mutation: str) -> None:
    if mutation in {row[1] for row in LEGACY_DAG_CONTROLS}:
        v1.mutate_fixture(fixture["legacy_fixture"], mutation)
    elif mutation == "declared_graph_differs_from_schema_graph":
        fixture["declared_edge_table"].pop()
    elif mutation == "schema_graph_differs_from_generation_order":
        fixture["generation_order"][0], fixture["generation_order"][1] = (
            fixture["generation_order"][1], fixture["generation_order"][0]
        )
    elif mutation == "undeclared_hash_bearing_field":
        schema = fixture["schemas"]["execution_source_manifest"]
        schema["properties"]["undeclared_registry_sha256"] = _sha_schema(
            "SOURCE_REGISTRY"
        )
        schema["required"].append("undeclared_registry_sha256")
    elif mutation == "later_phase_artifact_required_too_early":
        schema = fixture["schemas"]["execution_source_manifest"]
        schema["properties"]["future_review_inventory_sha256"] = _sha_schema(
            "INDEPENDENT_REVIEW_CONSUMER_INVENTORY"
        )
        schema["required"].append("future_review_inventory_sha256")
        fixture["reviewed_edge_table"] = derive_schema_edges(fixture["schemas"])
        fixture["declared_edge_table"] = deepcopy(fixture["reviewed_edge_table"])
        fixture["artifact_phases"] = None
    elif mutation == "consumer_map_truncated_to_one_row":
        fixture["candidate_consumer_rows"] = fixture["candidate_consumer_rows"][:1]
    elif mutation == "trace_truncated_to_match_consumer_map":
        fixture["runtime_trace_consumer_ids"] = fixture["runtime_trace_consumer_ids"][:1]
    elif mutation == "consumer_map_and_trace_locally_rebound":
        fixture["candidate_consumer_rows"] = fixture["candidate_consumer_rows"][:1]
        fixture["runtime_trace_consumer_ids"] = [
            fixture["candidate_consumer_rows"][0]["consumer_id"]
        ]
        fixture["candidate_local_rebound"] = True
    elif mutation == "stale_historical_count_treated_as_current_truth":
        fixture["candidate_expected_consumer_count"] = 520
    elif mutation == "fresh_consumer_omitted":
        fixture["candidate_consumer_rows"].pop()
    elif mutation == "invented_consumer_inserted":
        invented = deepcopy(fixture["candidate_consumer_rows"][0])
        invented["path"] = "invented/consumer.py"
        invented["consumer_id"] = _summary_consumer_id(invented)
        fixture["candidate_consumer_rows"].append(invented)
    elif mutation == "runtime_required_consumer_classified_nonruntime":
        next(
            row for row in fixture["candidate_consumer_rows"] if row["runtime_required"]
        )["runtime_required"] = False
    elif mutation == "baseline_path_changed_without_delta_classification":
        fixture["baseline_delta_changed_paths"] = []
    elif mutation == "preflight_inventory_altered_after_source_manifest_creation":
        fixture["preflight_sha256"] = "f" * 64
    elif mutation == "consumer_inventory_derived_from_candidate":
        fixture["candidate_inventory_origin"] = "CANDIDATE_SELF_DESCRIPTION"
    elif mutation == "review_trusts_execution_inventory_without_rescan":
        fixture["review_inventory_origin"] = "EXECUTION_PREFLIGHT_ATTESTATION"
    else:
        raise ValueError(f"unknown v2 mutation: {mutation}")


def _draft_run_negative_controls() -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    for control_id, mutation, expected in LEGACY_DAG_CONTROLS + V2_NEGATIVE_CONTROLS:
        if mutation in {row[1] for row in V2_NEGATIVE_CONTROLS[4:]}:
            baseline = build_lifecycle_fixture("COMPLETE")
            validate_cross_document_lifecycle(baseline)
            baseline_sha = sha256(compact_json_bytes(baseline))
            candidate = deepcopy(baseline)
            mutate_cross_document_fixture(candidate, mutation)
            try:
                validate_cross_document_lifecycle(candidate)
                observed = None
            except V2PreparationError as error:
                observed = error.code
        else:
            baseline = _draft_positive_lifecycle_fixture("COMPLETE")
            _draft_validate_lifecycle_fixture(baseline, "COMPLETE")
            baseline_sha = sha256(compact_json_bytes(baseline))
            candidate = deepcopy(baseline)
            _draft_mutate_lifecycle_fixture(candidate, mutation)
            try:
                _draft_validate_lifecycle_fixture(candidate, "COMPLETE")
                observed = None
            except V2PreparationError as error:
                observed = error.code
        results.append(
            {
                "baseline_recreated": True,
                "baseline_sha256_after": baseline_sha,
                "baseline_sha256_before": baseline_sha,
                "control_id": control_id,
                "expected_error_code": expected,
                "mutation": mutation,
                "observed_error_code": observed,
                "passed": observed == expected,
                "subsequent_controls_unmodified": True,
            }
        )
    failures = [row for row in results if not row["passed"]]
    if failures:
        raise V2PreparationError(f"V2-E-NEGATIVE-CONTROL-FAILURE:{failures}")
    return results


def _git_literal_consumer_paths(commit: str) -> set[str]:
    result = subprocess.run(
        [
            "git",
            "grep",
            "-l",
            "-F",
            "LOOP_CONTROL_REGISTRY_v0.json",
            commit,
            "--",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    prefix = commit + ":"
    paths = {
        line[len(prefix) :] if line.startswith(prefix) else line
        for line in result.stdout.splitlines()
        if line.strip()
    }
    paths.discard(REGISTRY_REL)
    return paths


def _git_tree_blob_map(commit: str) -> dict[str, str]:
    result = subprocess.run(
        [
            "git",
            "ls-tree",
            "-r",
            "--full-tree",
            "--format=%(objectname) %(path)",
            commit,
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    output: dict[str, str] = {}
    for line in result.stdout.splitlines():
        object_name, path = line.split(" ", 1)
        output[path] = object_name
    return output


def _legacy_runtime_required(path: str, raw: bytes) -> bool:
    if path in NONLITERAL_READERS or path == (
        "formal/python/tools/loop_control_registry_integrity.py"
    ):
        return True
    if Path(path).suffix.lower() != ".py":
        return False
    text = raw.decode("utf-8", errors="replace")
    return any(token in text for token in ("read_text", "read_bytes", "json.load", "open("))


_LEGACY_PATH_SCAN_CACHE: dict[str, dict[str, Any]] = {}


def legacy_path_scan_evidence(commit: str) -> dict[str, Any]:
    """Reproduce the historical path-level algorithm as non-normative evidence."""

    if commit in _LEGACY_PATH_SCAN_CACHE:
        return deepcopy(_LEGACY_PATH_SCAN_CACHE[commit])

    baseline = _strict_json(_git_blob(SOURCE_COMMIT, BASELINE_CONSUMER_REL))
    baseline_by_path = {row["path"]: row for row in baseline["consumers"]}
    baseline_paths = set(baseline_by_path)
    literal = _git_literal_consumer_paths(commit)
    current = literal | set(NONLITERAL_READERS)
    tree = _git_tree_blob_map(commit)
    added = sorted(current - baseline_paths)
    removed = sorted(baseline_paths - current)
    changed = sorted(
        path
        for path in baseline_paths & current
        if tree[path] != baseline_by_path[path]["git_blob"]
    )
    unchanged = (baseline_paths & current) - set(changed)
    runtime_required = sum(
        bool(baseline_by_path[path]["runtime_trace_required"])
        for path in unchanged
    ) + sum(
        _legacy_runtime_required(path, _git_blob(commit, path))
        for path in sorted(set(added) | set(changed))
    )
    output = {
        "added_path_count": len(added),
        "added_paths": added,
        "baseline_path_count": len(baseline_paths),
        "changed_baseline_path_count": len(changed),
        "changed_baseline_paths": changed,
        "exact_literal_path_count": len(literal),
        "explicit_nonliteral_path_count": len(NONLITERAL_READERS),
        "nonruntime_path_count": len(current) - runtime_required,
        "path_count": len(current),
        "removed_path_count": len(removed),
        "removed_paths": removed,
        "runtime_required_path_count": runtime_required,
        "scan_commit": commit,
        "sorted_path_lf_root_sha256": sha256(
            "\n".join(sorted(current)).encode("utf-8")
        ),
    }
    _LEGACY_PATH_SCAN_CACHE[commit] = deepcopy(output)
    return output


def consumer_inventory_algorithm_contract() -> dict[str, Any]:
    return {
        "algorithm_id": "LOOP_CONTROL_CONSUMER_DISCOVERY_CALLSITE_v2",
        "authoritative_input": (
            "EXACT_GIT_COMMIT_TREE_AND_BLOBS_LOADED_WITH_GIT_LS_TREE_AND_CAT_FILE"
        ),
        "candidate_or_worktree_input_permitted": False,
        "scan_unit": "ONE_ROW_PER_DISTINCT_CALL_SITE_OR_REFERENCE_FINDING",
        "discovery_pass_order": [
            "ENUMERATE_EXACT_COMMIT_TREE",
            "SCAN_EVERY_NONREGISTRY_BLOB_FOR_EXACT_REGISTRY_BASENAME_BYTES",
            "ADD_FROZEN_REVIEWED_NONLITERAL_PATH_RULES",
        ],
        "execution_scanner_implementation": (
            "GIT_GREP_PATH_ENUMERATION_PLUS_GIT_CAT_FILE_EXACT_BLOB_SCAN_v2"
        ),
        "independent_review_scanner_implementation": (
            "FULL_TREE_ENUMERATION_PLUS_INDEPENDENT_CAT_FILE_BLOB_SCAN_v2"
        ),
        "scanner_implementations_must_be_distinct": True,
        "consumer_categories": CONSUMER_CATEGORIES,
        "category_precedence": [
            "GENERATED_REFERENCE",
            "HISTORICAL_ONLY",
            "DOCUMENTATION_ONLY",
            "TEST_ONLY",
            "WRITER",
            "DYNAMIC_READER",
            "INDIRECT_API_CONSUMER",
            "DIRECT_READER",
        ],
        "operation_classes": OPERATION_CLASSES,
        "discovery_mechanisms": DISCOVERY_MECHANISMS,
        "runtime_required_categories": RUNTIME_REQUIRED_CATEGORIES,
        "runtime_required_is_derived_not_candidate_supplied": True,
        "statement_or_call_site_commitment": {
            "literal_occurrence": (
                "SHA256_OF_DOMAIN_SEPARATED_CANONICAL_DESCRIPTOR_BINDING_"
                "PATH_GIT_BLOB_BYTE_START_BYTE_END_AND_EXACT_MATCHED_BYTES_SHA256"
            ),
            "reviewed_nonliteral_rule": (
                "SHA256_OF_DOMAIN_SEPARATED_CANONICAL_DESCRIPTOR_BINDING_"
                "PATH_GIT_BLOB_FROZEN_RULE_ID_AND_EXACT_SOURCE_SHA256"
            ),
            "candidate_supplied_statement_or_locator_permitted": False,
        },
        "classification_rule": (
            "FROZEN_PATH_SUFFIX_AND_RUNTIME_SIGNAL_PRECEDENCE_TABLE_IN_CONTRACT"
        ),
        "runtime_signal_rule": (
            "NONLITERAL_RULE_PATH_OR_INTEGRITY_IMPLEMENTATION_OR_PYTHON_BLOB_"
            "CONTAINING_READ_TEXT_READ_BYTES_JSON_LOAD_OR_OPEN_TOKEN"
        ),
        "identity_fields": [
            "repository_relative_path",
            "consumer_category",
            "operation_class",
            "discovery_mechanism",
            "statement_or_call_site_sha256",
        ],
        "consumer_id_preimage": (
            "UTF8_LOOP_CONTROL_CONSUMER_ID_v2_NUL_PLUS_COMPACT_CANONICAL_"
            "JSON_OF_EXACT_IDENTITY_FIELDS"
        ),
        "consumer_id_format": "lcc2:PLUS_LOWERCASE_SHA256",
        "row_order": (
            "PATH_UTF8_BYTES_THEN_STATEMENT_SHA256_THEN_CATEGORY_THEN_"
            "OPERATION_CLASS_THEN_DISCOVERY_MECHANISM"
        ),
        "all_identity_root_preimage": (
            "UTF8_LOOP_CONTROL_ALL_CONSUMER_IDENTITIES_v2_NUL_PLUS_"
            "SORTED_CONSUMER_IDS_JOINED_LF_NO_TERMINAL_LF"
        ),
        "runtime_required_root_preimage": (
            "UTF8_LOOP_CONTROL_RUNTIME_REQUIRED_IDENTITIES_v2_NUL_PLUS_"
            "SORTED_DERIVED_RUNTIME_IDS_JOINED_LF_NO_TERMINAL_LF"
        ),
        "path_level_baseline_delta": (
            "COMPARE_BASELINE_GIT_BLOB_TO_CURRENT_GIT_BLOB_AND_CLASSIFY_"
            "EVERY_ADDED_CHANGED_REMOVED_PATH"
        ),
        "scan_failure": (
            "PREFLIGHT_BLOCKED_NONZERO_BOUNDED_DIAGNOSTIC_NO_PROTOTYPE_ROOT"
        ),
    }


def _identity(path: str, raw: bytes) -> dict[str, Any]:
    return {"path": path, "sha256": sha256(raw), "size_bytes": len(raw)}


def _git_fixture_identity(path: str, digest: str) -> dict[str, Any]:
    return {
        "git_blob": digest[0] * 40,
        "git_commit": "a" * 40,
        "path": path,
        "sha256": digest,
        "size_bytes": 1,
    }


MODEL_ACCEPTED_V2_CONTRACT_SHA256: Final = "7" * 64
MODEL_ACCEPTED_V2_REVIEW_SHA256: Final = "c" * 64


def _execution_git_identity(relative: str) -> dict[str, Any]:
    expected_sha, expected_oid, expected_size = EXPECTED_INPUTS[relative]
    return {
        "git_blob": expected_oid,
        "git_commit": SOURCE_COMMIT,
        "path": relative,
        "sha256": expected_sha,
        "size_bytes": expected_size,
    }


def _authorized_implementation_inventory_bytes() -> bytes:
    rows = [
        {
            "git_blob": EXPECTED_INPUTS[relative][1],
            "path": relative,
            "sha256": EXPECTED_INPUTS[relative][0],
            "size_bytes": EXPECTED_INPUTS[relative][2],
            "source_commit": SOURCE_COMMIT,
        }
        for relative in AUTHORIZED_IMPLEMENTATION_PATHS
    ]
    return compact_json_bytes(
        {
            "algorithm_id": "LOOP_CONTROL_AUTHORIZED_IMPLEMENTATION_SET_v2",
            "implementations": rows,
        }
    )


def _lifecycle_model_external_identities(
    schemas: dict[str, dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Independent expectations used by the executable lifecycle witness.

    The contract and review identities are symbolic future roots because this
    preparation cannot hash a not-yet-accepted independent review. Production
    resolves those two identities from the accepted v2 contract and review;
    every other identity below is derived from frozen source-commit bytes.
    """

    return {
        "ACCEPTED_V2_INDEPENDENT_REVIEW": _git_fixture_identity(
            "review/v2-independent-review.json",
            MODEL_ACCEPTED_V2_REVIEW_SHA256,
        ),
        "AUTHORIZED_IMPLEMENTATION": _identity(
            "implementation/authorized_inventory.json",
            _authorized_implementation_inventory_bytes(),
        ),
        "EXECUTION_PROTOCOL": _execution_git_identity(V3_PROTOCOL_REL),
        "SOURCE_REGISTRY": _execution_git_identity(REGISTRY_REL),
        "V2_CONTRACT": _git_fixture_identity(
            "review/v2-contract.json", MODEL_ACCEPTED_V2_CONTRACT_SHA256
        ),
        "V2_SCHEMA_BUNDLE": _identity(
            "review/embedded-v2-runtime-schemas.json",
            compact_json_bytes(schemas),
        ),
    }


def _consumer_id(row: dict[str, Any]) -> str:
    identity = {
        "repository_relative_path": row["path"],
        "consumer_category": row["consumer_category"],
        "operation_class": row["operation_class"],
        "discovery_mechanism": row["discovery_mechanism"],
        "statement_or_call_site_sha256": row["statement_or_call_site_sha256"],
    }
    return "lcc2:" + sha256(
        b"LOOP_CONTROL_CONSUMER_ID_v2\0" + compact_json_bytes(identity)
    )


_EXECUTION_CALLSITE_SCAN_CACHE: list[dict[str, Any]] | None = None
_INDEPENDENT_REVIEW_CALLSITE_SCAN_CACHE: list[dict[str, Any]] | None = None


def _execution_consumer_classification(
    path: str, source_raw: bytes, *, nonliteral: bool
) -> tuple[str, str, str]:
    runtime_signal = _legacy_runtime_required(path, source_raw)
    suffix = Path(path).suffix.lower()
    if nonliteral:
        category = "INDIRECT_API_CONSUMER"
    elif "/tests/" in f"/{path}":
        category = "TEST_ONLY"
    elif suffix in {".md", ".txt", ".lean"}:
        category = "DOCUMENTATION_ONLY"
    elif path.startswith(("archive/", "backup/")):
        category = "HISTORICAL_ONLY"
    elif path.startswith("formal/docs/release/") and suffix == ".json":
        category = "GENERATED_REFERENCE"
    elif "integrity" in path and runtime_signal:
        category = "WRITER"
    elif runtime_signal:
        category = "DIRECT_READER"
    else:
        category = "GENERATED_REFERENCE"
    if category not in RUNTIME_REQUIRED_CATEGORIES:
        operation = "LITERAL_REFERENCE_ONLY"
    elif category == "WRITER":
        operation = "MUTATE_REGISTRY"
    elif "schema" in path.lower() or "validat" in path.lower():
        operation = "VALIDATE_ROOT_SCHEMA"
    elif "hash" in path.lower() or "integrity" in path.lower():
        operation = "COMPARE_HASH"
    else:
        operation = "READ_CURRENT_AUTHORITY"
    mechanism = (
        "REVIEWED_NONLITERAL_PATH_RULE"
        if nonliteral
        else "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    )
    return category, operation, mechanism


def _execution_call_site_commitment(
    path: str,
    git_blob: str,
    source_raw: bytes,
    byte_start: int,
    byte_end: int,
    *,
    nonliteral: bool,
) -> str:
    if nonliteral:
        descriptor = {
            "git_blob": git_blob,
            "path": path,
            "rule_id": "FROZEN_NONLITERAL_READERS_v2",
            "source_sha256": sha256(source_raw),
        }
        domain = b"LOOP_CONTROL_REVIEWED_NONLITERAL_CALLSITE_v2\0"
    else:
        descriptor = {
            "byte_end": byte_end,
            "byte_start": byte_start,
            "git_blob": git_blob,
            "matched_bytes_sha256": sha256(source_raw[byte_start:byte_end]),
            "path": path,
        }
        domain = b"LOOP_CONTROL_LITERAL_CALLSITE_v2\0"
    return sha256(domain + compact_json_bytes(descriptor))


def _execution_scan_observation_commitment(row: dict[str, Any]) -> str:
    descriptor = {
        key: row[key]
        for key in (
            "byte_end",
            "byte_start",
            "discovery_mechanism",
            "git_blob",
            "path",
            "source_sha256",
            "statement_or_call_site_sha256",
        )
    }
    return sha256(
        b"LOOP_CONTROL_EXECUTION_PREFLIGHT_SCAN_OBSERVATION_v2\0"
        + compact_json_bytes(descriptor)
    )


def _fixture_repository_consumer_records() -> list[dict[str, Any]]:
    """Execution preflight scanner: Git grep path discovery plus blob scan."""

    global _EXECUTION_CALLSITE_SCAN_CACHE
    if _EXECUTION_CALLSITE_SCAN_CACHE is not None:
        return deepcopy(_EXECUTION_CALLSITE_SCAN_CACHE)
    baseline = _strict_json(_git_blob(SOURCE_COMMIT, BASELINE_CONSUMER_REL))
    baseline_by_path = {row["path"]: row for row in baseline["consumers"]}
    tree = _git_tree_blob_map(SOURCE_COMMIT)
    literal_paths = _git_literal_consumer_paths(SOURCE_COMMIT)
    requested_paths = literal_paths | set(NONLITERAL_READERS)
    if requested_paths - set(tree):
        raise V2PreparationError("V2-E-CONSUMER-DYNAMIC-PATH-MISSING")
    source_cache = _git_blobs(SOURCE_COMMIT, requested_paths)
    needle = b"LOOP_CONTROL_REGISTRY_v0.json"
    findings: list[tuple[str, int, int, bool]] = []
    for path in sorted(literal_paths, key=lambda value: value.encode("utf-8")):
        source_raw = source_cache[path]
        offset = 0
        while True:
            found = source_raw.find(needle, offset)
            if found < 0:
                break
            findings.append((path, found, found + len(needle), False))
            offset = found + len(needle)
    findings.extend(
        (path, 0, max(1, len(source_cache[path])), True)
        for path in NONLITERAL_READERS
    )

    rows: list[dict[str, Any]] = []
    for path, byte_start, byte_end, nonliteral in findings:
        source_raw = source_cache[path]
        source_sha = sha256(source_raw)
        category, operation, mechanism = _execution_consumer_classification(
            path, source_raw, nonliteral=nonliteral
        )
        baseline_row = baseline_by_path.get(path)
        delta_class = (
            "ADDED"
            if baseline_row is None
            else "CHANGED"
            if baseline_row["git_blob"] != tree[path]
            else "UNCHANGED"
        )
        row = {
            "baseline_delta_class": delta_class,
            "byte_end": byte_end,
            "byte_start": byte_start,
            "consumer_category": category,
            "discovery_mechanism": mechanism,
            "git_blob": tree[path],
            "operation_class": operation,
            "path": path,
            "runtime_required": category in RUNTIME_REQUIRED_CATEGORIES,
            "source_sha256": source_sha,
            "statement_or_call_site_sha256": _execution_call_site_commitment(
                path,
                tree[path],
                source_raw,
                byte_start,
                byte_end,
                nonliteral=nonliteral,
            ),
        }
        row["scan_observation_sha256"] = (
            _execution_scan_observation_commitment(row)
        )
        rows.append(row)
    if not rows:
        raise V2PreparationError("V2-E-CONSUMER-RESCAN-FAILURE")
    _EXECUTION_CALLSITE_SCAN_CACHE = deepcopy(rows)
    return rows


def _consumer_rows() -> list[dict[str, Any]]:
    rows = _fixture_repository_consumer_records()
    for row in rows:
        row["consumer_id"] = _consumer_id(row)
    return sorted(
        rows,
        key=lambda row: (
            row["path"].encode("utf-8"),
            row["statement_or_call_site_sha256"],
            row["consumer_category"],
            row["operation_class"],
            row["discovery_mechanism"],
        ),
    )


def _independent_review_consumer_id(row: dict[str, Any]) -> str:
    """Independent implementation of the reviewed identity preimage."""

    identity = {
        "consumer_category": row["consumer_category"],
        "discovery_mechanism": row["discovery_mechanism"],
        "operation_class": row["operation_class"],
        "repository_relative_path": row["path"],
        "statement_or_call_site_sha256": row[
            "statement_or_call_site_sha256"
        ],
    }
    serialized = json.dumps(
        identity,
        allow_nan=False,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return "lcc2:" + hashlib.sha256(
        b"LOOP_CONTROL_CONSUMER_ID_v2\0" + serialized
    ).hexdigest()


def _independent_review_runtime_signal(path: str, raw: bytes) -> bool:
    if path in NONLITERAL_READERS or path == (
        "formal/python/tools/loop_control_registry_integrity.py"
    ):
        return True
    if Path(path).suffix.lower() != ".py":
        return False
    decoded = raw.decode("utf-8", errors="replace")
    return any(
        marker in decoded
        for marker in ("read_text", "read_bytes", "json.load", "open(")
    )


def _independent_review_classification(
    path: str, source_raw: bytes, *, nonliteral: bool
) -> tuple[str, str, str]:
    signal = _independent_review_runtime_signal(path, source_raw)
    extension = Path(path).suffix.lower()
    if nonliteral:
        category = "INDIRECT_API_CONSUMER"
    elif "/tests/" in "/" + path:
        category = "TEST_ONLY"
    elif extension in (".md", ".txt", ".lean"):
        category = "DOCUMENTATION_ONLY"
    elif path.startswith("archive/") or path.startswith("backup/"):
        category = "HISTORICAL_ONLY"
    elif path.startswith("formal/docs/release/") and extension == ".json":
        category = "GENERATED_REFERENCE"
    elif "integrity" in path and signal:
        category = "WRITER"
    elif signal:
        category = "DIRECT_READER"
    else:
        category = "GENERATED_REFERENCE"
    if category not in set(RUNTIME_REQUIRED_CATEGORIES):
        operation = "LITERAL_REFERENCE_ONLY"
    elif category == "WRITER":
        operation = "MUTATE_REGISTRY"
    elif "schema" in path.lower() or "validat" in path.lower():
        operation = "VALIDATE_ROOT_SCHEMA"
    elif "hash" in path.lower() or "integrity" in path.lower():
        operation = "COMPARE_HASH"
    else:
        operation = "READ_CURRENT_AUTHORITY"
    mechanism = (
        "REVIEWED_NONLITERAL_PATH_RULE"
        if nonliteral
        else "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    )
    return category, operation, mechanism


def _independent_review_call_site_commitment(
    path: str,
    git_blob: str,
    source_raw: bytes,
    byte_start: int,
    byte_end: int,
    *,
    nonliteral: bool,
) -> str:
    if nonliteral:
        value = {
            "source_sha256": hashlib.sha256(source_raw).hexdigest(),
            "rule_id": "FROZEN_NONLITERAL_READERS_v2",
            "path": path,
            "git_blob": git_blob,
        }
        prefix = b"LOOP_CONTROL_REVIEWED_NONLITERAL_CALLSITE_v2\0"
    else:
        value = {
            "path": path,
            "matched_bytes_sha256": hashlib.sha256(
                source_raw[byte_start:byte_end]
            ).hexdigest(),
            "git_blob": git_blob,
            "byte_start": byte_start,
            "byte_end": byte_end,
        }
        prefix = b"LOOP_CONTROL_LITERAL_CALLSITE_v2\0"
    encoded = json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return hashlib.sha256(prefix + encoded).hexdigest()


def _independent_review_scan_observation_commitment(
    row: dict[str, Any],
) -> str:
    value = {
        "statement_or_call_site_sha256": row[
            "statement_or_call_site_sha256"
        ],
        "source_sha256": row["source_sha256"],
        "path": row["path"],
        "git_blob": row["git_blob"],
        "discovery_mechanism": row["discovery_mechanism"],
        "byte_start": row["byte_start"],
        "byte_end": row["byte_end"],
    }
    encoded = json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return hashlib.sha256(
        b"LOOP_CONTROL_INDEPENDENT_REVIEW_SCAN_OBSERVATION_v2\0" + encoded
    ).hexdigest()


def _independent_review_repository_consumer_records() -> list[dict[str, Any]]:
    """Independent review scanner: enumerate and inspect every Git blob."""

    global _INDEPENDENT_REVIEW_CALLSITE_SCAN_CACHE
    if _INDEPENDENT_REVIEW_CALLSITE_SCAN_CACHE is not None:
        return deepcopy(_INDEPENDENT_REVIEW_CALLSITE_SCAN_CACHE)
    baseline_raw = _git_blob(SOURCE_COMMIT, BASELINE_CONSUMER_REL)
    baseline_document = json.loads(baseline_raw.decode("utf-8"))
    baseline_by_path = {
        item["path"]: item for item in baseline_document["consumers"]
    }
    listing = subprocess.run(
        [
            "git",
            "ls-tree",
            "-r",
            "-z",
            "--full-tree",
            "--format=%(objectname) %(path)",
            SOURCE_COMMIT,
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        check=True,
    ).stdout
    entries: list[tuple[str, str]] = []
    for encoded_entry in listing.split(b"\0"):
        if not encoded_entry:
            continue
        object_name, encoded_path = encoded_entry.split(b" ", 1)
        entries.append(
            (
                object_name.decode("ascii"),
                encoded_path.decode("utf-8", errors="strict"),
            )
        )
    tree = {path: object_name for object_name, path in entries}
    paths_by_object: dict[str, list[str]] = {}
    for object_name, path in entries:
        paths_by_object.setdefault(object_name, []).append(path)

    needle = b"LOOP_CONTROL_REGISTRY_v0.json"
    findings: list[tuple[str, bytes, int, int, bool]] = []
    seen_nonliteral: set[str] = set()
    process = subprocess.Popen(
        ["git", "cat-file", "--batch"],
        cwd=REPO_ROOT,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        ordered_objects = sorted(paths_by_object)
        batch_output, stderr = process.communicate(
            input=(
            b"".join(
                object_name.encode("ascii") + b"\n"
                for object_name in ordered_objects
            )
            )
        )
        if process.returncode != 0:
            raise V2PreparationError(
                "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED:"
                + stderr.decode("utf-8", errors="replace")[:200]
            )
        stream = io.BytesIO(batch_output)
        for requested_object in ordered_objects:
            header = stream.readline().rstrip(b"\n")
            parts = header.split(b" ")
            if len(parts) != 3:
                raise V2PreparationError(
                    "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"
                )
            observed_object = parts[0].decode("ascii")
            object_type = parts[1].decode("ascii")
            object_size = int(parts[2])
            source_raw = stream.read(object_size)
            if stream.read(1) != b"\n":
                raise V2PreparationError(
                    "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"
                )
            if observed_object != requested_object:
                raise V2PreparationError(
                    "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"
                )
            if object_type != "blob":
                continue
            for path in paths_by_object[requested_object]:
                if path == REGISTRY_REL:
                    continue
                if path in NONLITERAL_READERS:
                    findings.append(
                        (path, source_raw, 0, max(1, len(source_raw)), True)
                    )
                    seen_nonliteral.add(path)
                cursor = 0
                while True:
                    position = source_raw.find(needle, cursor)
                    if position < 0:
                        break
                    findings.append(
                        (
                            path,
                            source_raw,
                            position,
                            position + len(needle),
                            False,
                        )
                    )
                    cursor = position + len(needle)
    except Exception:
        if process.poll() is None:
            process.kill()
            process.wait()
        raise
    if seen_nonliteral != set(NONLITERAL_READERS):
        raise V2PreparationError(
            "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"
        )

    rows: list[dict[str, Any]] = []
    for path, source_raw, byte_start, byte_end, nonliteral in findings:
        if path not in tree:
            raise V2PreparationError("V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED")
        source_digest = hashlib.sha256(source_raw).hexdigest()
        category, operation, mechanism = _independent_review_classification(
            path, source_raw, nonliteral=nonliteral
        )
        baseline_row = baseline_by_path.get(path)
        classification = (
            "ADDED"
            if baseline_row is None
            else "CHANGED"
            if baseline_row["git_blob"] != tree[path]
            else "UNCHANGED"
        )
        row = {
            "baseline_delta_class": classification,
            "byte_end": byte_end,
            "byte_start": byte_start,
            "consumer_category": category,
            "discovery_mechanism": mechanism,
            "git_blob": tree[path],
            "operation_class": operation,
            "path": path,
            "runtime_required": category in set(RUNTIME_REQUIRED_CATEGORIES),
            "source_sha256": source_digest,
            "statement_or_call_site_sha256": (
                _independent_review_call_site_commitment(
                    path,
                    tree[path],
                    source_raw,
                    byte_start,
                    byte_end,
                    nonliteral=nonliteral,
                )
            ),
        }
        row["scan_observation_sha256"] = (
            _independent_review_scan_observation_commitment(row)
        )
        rows.append(row)
    if not rows:
        raise V2PreparationError("V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED")
    _INDEPENDENT_REVIEW_CALLSITE_SCAN_CACHE = deepcopy(rows)
    return rows


def _independent_review_consumer_rows() -> list[dict[str, Any]]:
    rows = _independent_review_repository_consumer_records()
    for row in rows:
        row["consumer_id"] = _independent_review_consumer_id(row)
    return sorted(
        rows,
        key=lambda row: (
            row["path"].encode("utf-8"),
            row["statement_or_call_site_sha256"],
            row["consumer_category"],
            row["operation_class"],
            row["discovery_mechanism"],
        ),
    )


def _execution_baseline_delta_rows(
    rows: list[dict[str, Any]],
) -> list[dict[str, str]]:
    baseline = _strict_json(_git_blob(SOURCE_COMMIT, BASELINE_CONSUMER_REL))
    baseline_by_path = {row["path"]: row for row in baseline["consumers"]}
    baseline_paths = set(baseline_by_path)
    current_paths = {row["path"] for row in rows}
    tree = _git_tree_blob_map(SOURCE_COMMIT)
    pairs = {
        ("ADDED", path) for path in current_paths - baseline_paths
    } | {
        ("REMOVED", path) for path in baseline_paths - current_paths
    } | {
        ("CHANGED", path)
        for path in current_paths & baseline_paths
        if tree[path] != baseline_by_path[path]["git_blob"]
    }
    return [
        {"classification": classification, "path": path}
        for classification, path in sorted(
            pairs, key=lambda item: (item[1].encode("utf-8"), item[0])
        )
    ]


def _independent_review_baseline_delta_rows(
    rows: list[dict[str, Any]],
) -> list[dict[str, str]]:
    baseline_document = json.loads(
        _git_blob(SOURCE_COMMIT, BASELINE_CONSUMER_REL).decode("utf-8")
    )
    baseline = {
        item["path"]: item for item in baseline_document["consumers"]
    }
    current = {item["path"] for item in rows}
    commit_tree = _git_tree_blob_map(SOURCE_COMMIT)
    output: list[dict[str, str]] = []
    for path in sorted(set(baseline) | current, key=lambda value: value.encode("utf-8")):
        if path not in baseline:
            classification = "ADDED"
        elif path not in current:
            classification = "REMOVED"
        elif commit_tree[path] != baseline[path]["git_blob"]:
            classification = "CHANGED"
        else:
            continue
        output.append({"classification": classification, "path": path})
    return output


def _consumer_reconciliation_projection(row: dict[str, Any]) -> dict[str, Any]:
    """Fields that must agree across scanners; observation proof is domain-local."""

    return {
        key: row[key]
        for key in row
        if key != "scan_observation_sha256"
    }


def _identity_root(ids: Iterable[str], *, review: bool = False) -> str:
    domain = (
        b"LOOP_CONTROL_INDEPENDENT_REVIEW_IDENTITIES_v2\0"
        if review
        else b"LOOP_CONTROL_ALL_CONSUMER_IDENTITIES_v2\0"
    )
    return sha256(domain + "\n".join(sorted(ids)).encode("utf-8"))


def _runtime_identity_root(ids: Iterable[str], *, review: bool = False) -> str:
    domain = (
        b"LOOP_CONTROL_INDEPENDENT_REVIEW_RUNTIME_IDENTITIES_v2\0"
        if review
        else b"LOOP_CONTROL_RUNTIME_REQUIRED_IDENTITIES_v2\0"
    )
    return sha256(domain + "\n".join(sorted(ids)).encode("utf-8"))


def _delta_root(rows: list[dict[str, str]], *, review: bool = False) -> str:
    domain = (
        b"LOOP_CONTROL_INDEPENDENT_REVIEW_BASELINE_DELTA_v2\0"
        if review
        else b"LOOP_CONTROL_BASELINE_DELTA_v2\0"
    )
    return sha256(
        domain
        + b"\n".join(
            compact_json_bytes(row)
            for row in sorted(rows, key=lambda row: (row["path"], row["classification"]))
        )
    )


def _pre_run_inventory_root() -> str:
    rows = [
        {
            "git_blob": EXPECTED_INPUTS[REGISTRY_REL][1],
            "path": REGISTRY_REL,
            "sha256": REGISTRY_SHA256,
            "size_bytes": EXPECTED_INPUTS[REGISTRY_REL][2],
        }
    ]
    return sha256(
        b"LOOP_CONTROL_PRE_RUN_INVENTORY_SET_v2\0"
        + b"\n".join(compact_json_bytes(row) for row in rows)
    )


def _allowed_output_paths_root() -> str:
    return sha256(
        b"LOOP_CONTROL_ALLOWED_OUTPUT_PATH_SET_v2\0"
        + "\n".join(sorted(PRODUCTION_LAYOUT_PATHS)).encode("utf-8")
    )


def _artifact_root(rows: list[dict[str, Any]], domain: bytes) -> str:
    normalized = [
        {
            "artifact_type": row["artifact_type"],
            "path": row["path"],
            "sha256": row["sha256"],
            "size_bytes": row["size_bytes"],
        }
        for row in sorted(rows, key=lambda row: row["path"].encode("utf-8"))
    ]
    return sha256(domain + b"\0" + b"\n".join(compact_json_bytes(row) for row in normalized))


def _stage_a_control_results_root(rows: list[dict[str, Any]]) -> str:
    return sha256(
        b"LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v2\0"
        + b"\n".join(compact_json_bytes(row) for row in rows)
    )


_STAGE_A_PROFILE_CACHE: list[dict[str, Any]] | None = None


def _stage_a_profiles() -> list[dict[str, Any]]:
    global _STAGE_A_PROFILE_CACHE
    if _STAGE_A_PROFILE_CACHE is None:
        _STAGE_A_PROFILE_CACHE = v1._v0_stage_a_control_profiles()
    return deepcopy(_STAGE_A_PROFILE_CACHE)


def _put_document(
    documents: dict[str, dict[str, Any]],
    artifact_bytes: dict[str, bytes],
    artifact_type: str,
    document: dict[str, Any],
) -> None:
    documents[artifact_type] = document
    artifact_bytes[artifact_type] = canonical_json_bytes(document)


def _candidate_row(
    artifact_type: str, path: str, raw: bytes
) -> dict[str, Any]:
    return {"artifact_type": artifact_type, **_identity(path, raw)}


def _minimal_schema_instance(schema: dict[str, Any]) -> Any:
    """Construct a deterministic schema-valid baseline before hash rebinding."""

    if "const" in schema:
        return deepcopy(schema["const"])
    if "enum" in schema:
        return deepcopy(schema["enum"][0])
    schema_type = schema.get("type")
    if isinstance(schema_type, list):
        schema_type = next(item for item in schema_type if item != "null")
    if schema_type == "object" or "properties" in schema:
        value = {
            name: _minimal_schema_instance(schema["properties"][name])
            for name in schema.get("required", [])
        }
        for child in schema.get("allOf", []):
            if isinstance(child, dict) and (
                child.get("type") == "object" or "properties" in child
            ):
                value.update(_minimal_schema_instance(child))
        if schema.get("oneOf"):
            child = schema["oneOf"][0]
            if isinstance(child, dict) and (
                child.get("type") == "object" or "properties" in child
            ):
                value.update(_minimal_schema_instance(child))
        return value
    if schema_type == "array":
        return [
            _minimal_schema_instance(schema["items"])
            for _ in range(schema.get("minItems", 0))
        ]
    if schema_type == "string" or "pattern" in schema:
        pattern = schema.get("pattern", "")
        if pattern == "^[0-9a-f]{64}$":
            return "0" * 64
        if pattern == "^[0-9a-f]{40}$":
            return "a" * 40
        if pattern.startswith("^lcr1:"):
            return "lcr1:" + "0" * 64
        if pattern.startswith("^lcs1:"):
            return "lcs1:" + "0" * 64
        if pattern == "^(?:|(?:/(?:[^~/]|~[01])*)+)$":
            return ""
        if schema.get("contentEncoding") == "base64":
            return "e30="
        if "LOOP_CONTROL_HISTORY_" in pattern:
            return "history/shards/LOOP_CONTROL_HISTORY_0000.jsonl"
        if pattern.startswith("^[A-Za-z0-9]"):
            return "fixture"
        return "fixture/path.json" if "maxLength" in schema else "x" * max(
            1, schema.get("minLength", 1)
        )
    if schema_type == "integer":
        return schema.get("minimum", 0)
    if schema_type == "number":
        return schema.get("minimum", 0)
    if schema_type == "boolean":
        return False
    if schema.get("oneOf"):
        return _minimal_schema_instance(schema["oneOf"][0])
    raise V2PreparationError("V2-E-SCHEMA-POSITIVE-INSTANCE-CONSTRUCTION")


def _bind_schema_hash_targets(
    instance: Any, schema: dict[str, Any], target_hashes: dict[str, str]
) -> None:
    if not isinstance(instance, (dict, list)):
        return
    properties = schema.get("properties")
    if isinstance(instance, dict) and isinstance(properties, dict):
        for name, child_schema in properties.items():
            if name not in instance:
                continue
            annotation = (
                child_schema.get("x-toe-hash-edge")
                if isinstance(child_schema, dict)
                else None
            )
            if isinstance(annotation, dict):
                target = annotation["referenced_artifact_type"]
                if target in target_hashes and "const" not in child_schema:
                    instance[name] = target_hashes[target]
            _bind_schema_hash_targets(instance[name], child_schema, target_hashes)
    if isinstance(instance, list) and isinstance(schema.get("items"), dict):
        for child in instance:
            _bind_schema_hash_targets(child, schema["items"], target_hashes)


def _inherited_fixture_document(
    schema: dict[str, Any], target_hashes: dict[str, str]
) -> dict[str, Any]:
    document = _minimal_schema_instance(schema)
    if not isinstance(document, dict):
        raise V2PreparationError("V2-E-SCHEMA-POSITIVE-INSTANCE-CONSTRUCTION")
    _bind_schema_hash_targets(document, schema, target_hashes)
    Draft202012Validator(schema).validate(document)
    return document


def _full_generation_ledger() -> list[str]:
    return [
        artifact
        for artifact, (_, _, kind) in sorted(
            ARTIFACT_PHASES.items(), key=lambda item: (item[1][1], item[0])
        )
        if kind != "EXTERNAL"
    ]


def _physical_generation_ledger() -> list[str]:
    return [
        artifact
        for artifact, (_, _, kind) in sorted(
            ARTIFACT_PHASES.items(), key=lambda item: (item[1][1], item[0])
        )
        if kind in {"ARTIFACT", "ARTIFACT_SET"}
    ]


def _modeled_operation_result_bytes(consumer_row: dict[str, Any]) -> bytes:
    return compact_json_bytes(
        {
            "consumer_id": consumer_row["consumer_id"],
            "operation_class": consumer_row["operation_class"],
            "result_schema_id": "LOOP_CONTROL_SEMANTIC_OPERATION_RESULT_v2",
            "source_registry_sha256": REGISTRY_SHA256,
            "status": "SEMANTIC_PARITY",
        }
    )


def build_lifecycle_fixture(branch: str) -> dict[str, Any]:
    if branch not in {"COMPLETE", "POST_GENERATION_BLOCKED"}:
        raise V2PreparationError(f"unknown lifecycle branch: {branch}")
    blocked = branch == "POST_GENERATION_BLOCKED"
    schemas = build_runtime_schemas()
    documents: dict[str, dict[str, Any]] = {}
    artifact_bytes: dict[str, bytes] = {}
    schema_names: dict[str, str] = {}
    run_id = "stage_a_v2_fixture"
    rows = _consumer_rows()
    all_ids = [row["consumer_id"] for row in rows]
    runtime_ids = [row["consumer_id"] for row in rows if row["runtime_required"]]
    all_root = _identity_root(all_ids)
    runtime_root = _runtime_identity_root(runtime_ids)
    delta_rows = _execution_baseline_delta_rows(rows)
    inventory_doc = {
        "schema_id": "LOOP_CONTROL_EXECUTION_PREFLIGHT_CONSUMER_INVENTORY_v2",
        "inventory_origin": "REPOSITORY_GIT_OBJECT_SCAN",
        "algorithm_id": "LOOP_CONTROL_CONSUMER_DISCOVERY_CALLSITE_v2",
        "scanner_implementation_id": (
            "EXECUTION_GIT_GREP_CAT_FILE_SCANNER_v2"
        ),
        "source_commit": SOURCE_COMMIT,
        "source_tree": SOURCE_TREE,
        "consumers": deepcopy(rows),
        "consumer_identity_count": len(rows),
        "consumer_identity_root_sha256": all_root,
        "runtime_required_count": len(runtime_ids),
        "runtime_required_identity_root_sha256": runtime_root,
        "nonruntime_count": len(rows) - len(runtime_ids),
        "unique_path_count": len({row["path"] for row in rows}),
        "baseline_delta_rows": delta_rows,
        "baseline_delta_root_sha256": _delta_root(delta_rows),
    }
    _put_document(
        documents,
        artifact_bytes,
        "PREFLIGHT_CONSUMER_INVENTORY",
        inventory_doc,
    )
    schema_names["PREFLIGHT_CONSUMER_INVENTORY"] = "preflight_consumer_inventory"

    external_identities = _lifecycle_model_external_identities(schemas)
    contract_id = external_identities["V2_CONTRACT"]
    registry_raw = _source_registry_bytes()
    registry_id = external_identities["SOURCE_REGISTRY"]
    schema_id = external_identities["V2_SCHEMA_BUNDLE"]
    protocol_id = external_identities["EXECUTION_PROTOCOL"]
    implementation_id = external_identities["AUTHORIZED_IMPLEMENTATION"]
    attestation_doc = {
        "schema_id": "LOOP_CONTROL_EXECUTION_PREFLIGHT_ATTESTATION_v2",
        "source_commit": SOURCE_COMMIT,
        "source_tree": SOURCE_TREE,
        "reviewed_contract": deepcopy(contract_id),
        "source_registry": deepcopy(registry_id),
        "schema_bundle": deepcopy(schema_id),
        "protocol_bundle": deepcopy(protocol_id),
        "implementation_inventory": deepcopy(implementation_id),
        "consumer_inventory": _identity(
            "preflight/consumer_inventory.json",
            artifact_bytes["PREFLIGHT_CONSUMER_INVENTORY"],
        ),
        "consumer_identity_count": len(rows),
        "consumer_identity_root_sha256": all_root,
        "runtime_required_count": len(runtime_ids),
        "runtime_required_identity_root_sha256": runtime_root,
        "nonruntime_count": len(rows) - len(runtime_ids),
        "baseline_delta_root_sha256": _delta_root(delta_rows),
        "candidate_supplied_inventory_used": False,
    }
    _put_document(
        documents,
        artifact_bytes,
        "EXECUTION_PREFLIGHT_ATTESTATION",
        attestation_doc,
    )
    schema_names["EXECUTION_PREFLIGHT_ATTESTATION"] = "execution_preflight_attestation"

    review_id = external_identities["ACCEPTED_V2_INDEPENDENT_REVIEW"]
    source_doc = {
        "schema_id": "LOOP_CONTROL_EXECUTION_SOURCE_MANIFEST_v3",
        "source_commit": SOURCE_COMMIT,
        "accepted_contract_review": deepcopy(review_id),
        "reviewed_contract": deepcopy(contract_id),
        "preflight_attestation": _identity(
            "manifests/preflight_attestation.json",
            artifact_bytes["EXECUTION_PREFLIGHT_ATTESTATION"],
        ),
        "source_registry": deepcopy(registry_id),
        "schema_bundle": deepcopy(schema_id),
        "protocol_bundle": deepcopy(protocol_id),
        "implementation_inventory": deepcopy(implementation_id),
        "consumer_identity_count": len(rows),
        "consumer_identity_root_sha256": all_root,
        "runtime_required_count": len(runtime_ids),
        "runtime_required_identity_root_sha256": runtime_root,
        "execution_command": EXECUTION_COMMAND,
        "runtime_output_count": 0,
        "immutable": True,
    }
    _put_document(documents, artifact_bytes, "SOURCE_MANIFEST", source_doc)
    schema_names["SOURCE_MANIFEST"] = "execution_source_manifest"

    map_doc = {
        "schema_id": "LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v4",
        "source_manifest": _identity(
            "manifests/source_manifest.json", artifact_bytes["SOURCE_MANIFEST"]
        ),
        "preflight_inventory": _identity(
            "preflight/consumer_inventory.json",
            artifact_bytes["PREFLIGHT_CONSUMER_INVENTORY"],
        ),
        "inventory_origin": "EXACT_PREFLIGHT_REPOSITORY_PROJECTION",
        "consumers": deepcopy(rows),
        "consumer_identity_count": len(rows),
        "consumer_identity_root_sha256": all_root,
        "runtime_required_count": len(runtime_ids),
        "runtime_required_identity_root_sha256": runtime_root,
        "nonruntime_count": len(rows) - len(runtime_ids),
        "status": "EXACT_PREFLIGHT_INVENTORY_RECONCILIATION_REQUIRED",
    }
    _put_document(documents, artifact_bytes, "CONSUMER_MAP", map_doc)
    schema_names["CONSUMER_MAP"] = "candidate_consumer_map"

    # Instantiate the inherited schemas as actual documents in the same
    # dependency order as the schema-derived graph.  The custody bytes are a
    # deterministic gzip member of the reviewed registry Git object.
    artifact_bytes["CUSTODY_PAYLOAD"] = _custody_payload_bytes()
    history_witness = _history_witness(schemas["history_shard_record"])
    target_hashes = {
        "AUTHORIZED_IMPLEMENTATION": implementation_id["sha256"],
        "CONSUMER_MAP": sha256(artifact_bytes["CONSUMER_MAP"]),
        "CUSTODY_CONTRACT": EXPECTED_INPUTS[CUSTODY_CONTRACT_REL][0],
        "CUSTODY_PAYLOAD": sha256(artifact_bytes["CUSTODY_PAYLOAD"]),
        "GUARDRAIL_PACKET": EXPECTED_INPUTS[GUARDRAIL_PACKET_REL][0],
        "GUARDRAIL_REVIEW": EXPECTED_INPUTS[GUARDRAIL_REVIEW_REL][0],
        "HISTORY_FULL_RECORD_IDENTITY_SET": (
            HISTORY_FULL_RECORD_IDENTITY_ROOT_SHA256
        ),
        "HISTORY_IDENTITY_PAYLOAD_POINTER_SET": (
            HISTORY_IDENTITY_PAYLOAD_POINTER_ROOT_SHA256
        ),
        "HISTORY_ORIGINAL_POINTER_SET": (
            HISTORY_ORIGINAL_POINTER_SET_SHA256
        ),
        "LEGACY_RECONSTRUCTED_BYTES": REGISTRY_SHA256,
        "SOURCE_REGISTRY": REGISTRY_SHA256,
        "SOURCE_REGISTRY_RECORD_PAYLOAD": sha256(b"{}"),
        "AUTHORITY_EVIDENCE": EXPECTED_INPUTS[MAINTENANCE_AUTHORITY_REL][0],
        "SOURCE_AUTHORITY_COMMITMENT": AUTHORITY_COMMITMENT_SHA256,
    }
    inherited_documents: list[tuple[str, str]] = [
        ("HISTORY_SHARD", "history_shard_record"),
        ("CUSTODY_MANIFEST", "legacy_byte_custody_manifest"),
        ("LEGACY_RECONSTRUCTION", "compatibility_reconstruction_result"),
        ("HISTORY_INDEX", "history_index"),
        ("CURRENT_PROJECTION", "current_projection"),
    ]
    for artifact_type, schema_name in inherited_documents:
        if artifact_type == "HISTORY_SHARD":
            documents[artifact_type] = deepcopy(
                history_witness["representative_record"]
            )
            artifact_bytes[artifact_type] = history_witness["set_bytes"]
            schema_names[artifact_type] = schema_name
            continue
        if artifact_type == "HISTORY_INDEX":
            target_hashes["HISTORY_SHARD"] = sha256(
                artifact_bytes["HISTORY_SHARD"]
            )
            target_hashes["CUSTODY_MANIFEST"] = sha256(
                artifact_bytes["CUSTODY_MANIFEST"]
            )
        elif artifact_type == "CURRENT_PROJECTION":
            target_hashes["HISTORY_INDEX"] = sha256(
                artifact_bytes["HISTORY_INDEX"]
            )
        document = _inherited_fixture_document(
            schemas[schema_name], target_hashes
        )
        if artifact_type == "CUSTODY_MANIFEST":
            document["generation_provenance"]["detached_checkout_commit"] = (
                SOURCE_COMMIT
            )
            document["gzip_profile"]["path"] = "custody/legacy.json.gz"
            document["payload_identity"].update(
                {
                    "compressed_size_bytes": len(
                        artifact_bytes["CUSTODY_PAYLOAD"]
                    ),
                    "path": "custody/legacy.json.gz",
                }
            )
            document["source_identity"] = {
                "git_blob": EXPECTED_INPUTS[REGISTRY_REL][1],
                "path": REGISTRY_REL,
                "sha256": REGISTRY_SHA256,
                "size_bytes": len(registry_raw),
                "source_commit": SOURCE_COMMIT,
            }
        elif artifact_type == "LEGACY_RECONSTRUCTION":
            document["clean_checkout_evidence"]["commit"] = SOURCE_COMMIT
            document["custody_payload_identity"].update(
                {
                    "path": "custody/legacy.json.gz",
                    "size_bytes": len(artifact_bytes["CUSTODY_PAYLOAD"]),
                }
            )
            document["reconstruction_identity"]["path"] = (
                "compat/reconstructed_registry.json"
            )
            document["source_identity"] = {
                "git_blob": EXPECTED_INPUTS[REGISTRY_REL][1],
                "path": REGISTRY_REL,
                "sha256": REGISTRY_SHA256,
                "size_bytes": len(registry_raw),
                "source_commit": SOURCE_COMMIT,
            }
        elif artifact_type == "HISTORY_INDEX":
            document["consumer_source_map_pointer"]["path"] = (
                "consumers/consumer_map.json"
            )
            document["custody_manifest_pointer"]["path"] = (
                "custody/manifest.json"
            )
            document["shards"] = deepcopy(history_witness["descriptors"])
            document["shard_count"] = len(document["shards"])
            document["source_registry_identity"] = {
                "git_blob": EXPECTED_INPUTS[REGISTRY_REL][1],
                "path": REGISTRY_REL,
                "sha256": REGISTRY_SHA256,
                "size_bytes": len(registry_raw),
                "source_commit": SOURCE_COMMIT,
            }
        elif artifact_type == "CURRENT_PROJECTION":
            document["history_index_pointer"]["path"] = "history/index.json"
            document["maintenance_authority"]["evidence"]["path"] = (
                MAINTENANCE_AUTHORITY_REL
            )
            document["maintenance_authority"]["current_maintenance_target"] = (
                MAINTENANCE_TARGET
            )
            document["scientific_authority"]["current_target"] = (
                SCIENTIFIC_TARGET
            )
            document["source_legacy_identity"] = {
                "git_blob": EXPECTED_INPUTS[REGISTRY_REL][1],
                "path": REGISTRY_REL,
                "sha256": REGISTRY_SHA256,
                "size_bytes": len(registry_raw),
                "source_commit": SOURCE_COMMIT,
            }
        Draft202012Validator(schemas[schema_name]).validate(document)
        _put_document(
            documents, artifact_bytes, artifact_type, document
        )
        schema_names[artifact_type] = schema_name

    trace_documents: list[dict[str, Any]] = []
    operation_result_bytes: dict[str, bytes] = {}
    for row_value in (row for row in rows if row["runtime_required"]):
        result_bytes = _modeled_operation_result_bytes(row_value)
        operation_result_bytes[row_value["consumer_id"]] = result_bytes
        result_sha256 = sha256(result_bytes)
        event = {
            "schema_id": "LOOP_CONTROL_SHADOW_TRACE_EVENT_v4",
            "run_id": run_id,
            "trace_id": "lct2:" + sha256(row_value["consumer_id"].encode("utf-8")),
            "consumer_id": row_value["consumer_id"],
            "consumer_path": row_value["path"],
            "consumer_source_sha256": row_value["source_sha256"],
            "operation_class": row_value["operation_class"],
            "candidate_result_sha256": result_sha256,
            "legacy_result_sha256": result_sha256,
            "semantic_parity": True,
            "write_attempted": row_value["consumer_category"] == "WRITER",
        }
        Draft202012Validator(schemas["runtime_trace_event"]).validate(event)
        trace_documents.append(event)
    artifact_bytes["RUNTIME_TRACE"] = b"".join(
        compact_json_bytes(event) + b"\n" for event in trace_documents
    )
    trace_manifest_doc = {
        "schema_id": "LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v4",
        "run_id": run_id,
        "source_manifest": _identity(
            "manifests/source_manifest.json", artifact_bytes["SOURCE_MANIFEST"]
        ),
        "preflight_inventory": _identity(
            "preflight/consumer_inventory.json",
            artifact_bytes["PREFLIGHT_CONSUMER_INVENTORY"],
        ),
        "consumer_map": _identity(
            "consumers/consumer_map.json", artifact_bytes["CONSUMER_MAP"]
        ),
        "runtime_trace": _identity("traces/runtime_trace.jsonl", artifact_bytes["RUNTIME_TRACE"]),
        "traced_consumer_identity_root_sha256": runtime_root,
        "runtime_required_identity_root_sha256": runtime_root,
        "event_count": len(trace_documents),
        "runtime_required_count": len(runtime_ids),
        "unmatched_trace_count": 0,
        "unobserved_runtime_required_count": 0,
        "status": "COMPLETE_PARITY",
    }
    _put_document(
        documents,
        artifact_bytes,
        "RUNTIME_TRACE_MANIFEST",
        trace_manifest_doc,
    )
    schema_names["RUNTIME_TRACE_MANIFEST"] = "runtime_trace_manifest"

    trust_doc = {
        "schema_id": "LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v2",
        "accepted_contract_review": deepcopy(review_id),
        "source_registry": deepcopy(registry_id),
        "schema_bundle": deepcopy(schema_id),
        "protocol_bundle": deepcopy(protocol_id),
        "authority_commitment_sha256": AUTHORITY_COMMITMENT_SHA256,
        "stage_b_authorized": False,
    }
    _put_document(documents, artifact_bytes, "REVIEWED_TRUST_ANCHORS", trust_doc)
    schema_names["REVIEWED_TRUST_ANCHORS"] = "reviewed_trust_anchors"
    rollback_doc = {
        "schema_id": "LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v2",
        "pre_run_inventory_sha256": _pre_run_inventory_root(),
        "allowed_output_paths_sha256": _allowed_output_paths_root(),
        "future_artifact_content_hashes_present": False,
    }
    _put_document(documents, artifact_bytes, "ROLLBACK_INVENTORY", rollback_doc)
    schema_names["ROLLBACK_INVENTORY"] = "rollback_inventory"
    writer_doc = {
        "schema_id": "LOOP_CONTROL_WRITER_PROBE_v2",
        "source_registry_write_attempted": False,
        "write_outside_run_root_count": 0,
        "passed": True,
    }
    _put_document(documents, artifact_bytes, "WRITER_PROBE", writer_doc)
    schema_names["WRITER_PROBE"] = "writer_probe"

    paths = {
        "CUSTODY_PAYLOAD": "custody/legacy.json.gz",
        "HISTORY_SHARD": "history/shards/history_0000.jsonl",
        "CONSUMER_MAP": "consumers/consumer_map.json",
        "CUSTODY_MANIFEST": "custody/manifest.json",
        "LEGACY_RECONSTRUCTION": "compat/reconstruction.json",
        "HISTORY_INDEX": "history/index.json",
        "CURRENT_PROJECTION": "projection/current.json",
        "RUNTIME_TRACE": "traces/runtime_trace.jsonl",
        "RUNTIME_TRACE_MANIFEST": "traces/runtime_trace_manifest.json",
        "REVIEWED_TRUST_ANCHORS": "authority/trust_anchors.json",
        "WRITER_PROBE": "validation/writer_probe.json",
        "ROLLBACK_INVENTORY": "manifests/rollback_inventory.json",
        "CONTROL_EVIDENCE": "validation/control_evidence.json",
        "VALIDATION_REPORT": "validation/validation_report.json",
    }
    core_types = [
        "CUSTODY_PAYLOAD",
        "HISTORY_SHARD",
        "CONSUMER_MAP",
        "CUSTODY_MANIFEST",
        "LEGACY_RECONSTRUCTION",
        "HISTORY_INDEX",
        "CURRENT_PROJECTION",
        "RUNTIME_TRACE",
        "RUNTIME_TRACE_MANIFEST",
        "REVIEWED_TRUST_ANCHORS",
        "WRITER_PROBE",
        "ROLLBACK_INVENTORY",
    ]

    def candidate_rows_for(types: Iterable[str]) -> list[dict[str, Any]]:
        output: list[dict[str, Any]] = []
        for kind in types:
            if kind == "HISTORY_SHARD":
                output.extend(
                    _candidate_row(kind, path, member_raw)
                    for path, member_raw in history_witness["members"].items()
                )
            else:
                output.append(
                    _candidate_row(kind, paths[kind], artifact_bytes[kind])
                )
        return output

    core_rows = candidate_rows_for(core_types)
    core_root = _artifact_root(core_rows, b"LOOP_CONTROL_CORE_DATA_ROOT_v2")
    validation_schema = schemas["validation_report"]
    validation_document = _minimal_schema_instance(
        validation_schema["oneOf"][1 if blocked else 0]
    )
    _bind_schema_hash_targets(
        validation_document,
        validation_schema["oneOf"][1 if blocked else 0],
        {
            "CORE_CANDIDATE_ARTIFACT_SET": core_root,
            "CONTROL_PROFILE": validation_schema["oneOf"][
                1 if blocked else 0
            ]["properties"]["profile_control_root_sha256"]["const"],
            "REVIEWED_TRUST_ANCHORS": sha256(
                artifact_bytes["REVIEWED_TRUST_ANCHORS"]
            ),
        },
    )
    Draft202012Validator(validation_schema).validate(validation_document)
    _put_document(
        documents,
        artifact_bytes,
        "VALIDATION_REPORT",
        validation_document,
    )
    schema_names["VALIDATION_REPORT"] = "validation_report"
    profiles = _stage_a_profiles()
    control_rows = [
        {
            "control_id": profile["control_id"],
            "baseline_core_candidate_root_sha256": core_root,
            "passed": not (blocked and index == 0),
            "observed_error_codes": (["FIXTURE-CONTROL-FAILED"] if blocked and index == 0 else []),
        }
        for index, profile in enumerate(profiles)
    ]
    control_doc = {
        "schema_id": "LOOP_CONTROL_STAGE_A_CONTROL_EVIDENCE_v2",
        "run_id": run_id,
        "control_results": control_rows,
        "control_result_count": 76,
        "baseline_core_candidate_root_sha256": core_root,
        "results_root_sha256": _stage_a_control_results_root(control_rows),
        "all_results_passed": not blocked,
        "status": "B_BLOCKED" if blocked else "ALL_76_CONTROLS_PASSED",
    }
    _put_document(documents, artifact_bytes, "CONTROL_EVIDENCE", control_doc)
    schema_names["CONTROL_EVIDENCE"] = "control_evidence"

    candidate_types = [*core_types, "CONTROL_EVIDENCE", "VALIDATION_REPORT"]
    candidate_rows = candidate_rows_for(candidate_types)
    candidate_root = _artifact_root(
        candidate_rows, b"LOOP_CONTROL_ALL_CANDIDATE_ARTIFACT_ROOT_v2"
    )
    runtime_doc = {
        "schema_id": "LOOP_CONTROL_STAGE_A_RUNTIME_MANIFEST_v3",
        "run_id": run_id,
        "source_manifest": _identity(
            "manifests/source_manifest.json", artifact_bytes["SOURCE_MANIFEST"]
        ),
        "candidate_artifacts": candidate_rows,
        "candidate_artifact_count": len(candidate_rows),
        "candidate_artifact_root_sha256": candidate_root,
        "environment": {
            "filesystem_encoding": "utf-8",
            "platform": "fixture",
            "python_version": "3.fixture",
        },
        "execution_command": source_doc["execution_command"],
        "status": "B_BLOCKED_CANDIDATE_PRESERVED" if blocked else "CANDIDATE_COMPLETE",
        "block_reason_codes": ["CONTROL-FAILED"] if blocked else [],
    }
    _put_document(documents, artifact_bytes, "RUNTIME_MANIFEST", runtime_doc)
    schema_names["RUNTIME_MANIFEST"] = "runtime_manifest"

    report_doc = {
        "schema_id": "LOOP_CONTROL_STAGE_A_EXECUTION_REPORT_v3",
        "run_id": run_id,
        "runtime_manifest": _identity(
            "manifests/runtime_manifest.json", artifact_bytes["RUNTIME_MANIFEST"]
        ),
        "control_evidence": _identity(
            paths["CONTROL_EVIDENCE"], artifact_bytes["CONTROL_EVIDENCE"]
        ),
        "preflight_consumer_identity_root_sha256": all_root,
        "candidate_consumer_identity_root_sha256": all_root,
        "runtime_required_identity_root_sha256": runtime_root,
        "validator_decisions": [
            {"decision_id": "CONSUMER-RECONCILIATION", "passed": True},
            {"decision_id": "CONTROL-OUTCOME", "passed": not blocked},
        ],
        "status": "B_BLOCKED_CANDIDATE_PRESERVED" if blocked else "STAGE_A_CANDIDATE_COMPLETE",
        "block_reason_codes": ["CONTROL-FAILED"] if blocked else [],
    }
    _put_document(documents, artifact_bytes, "EXECUTION_REPORT", report_doc)
    schema_names["EXECUTION_REPORT"] = "execution_report"

    terminal_doc = {
        "schema_id": "LOOP_CONTROL_STAGE_A_TERMINAL_ENVELOPE_v2",
        "run_id": run_id,
        "source_manifest": _identity(
            "manifests/source_manifest.json", artifact_bytes["SOURCE_MANIFEST"]
        ),
        "runtime_manifest": _identity(
            "manifests/runtime_manifest.json", artifact_bytes["RUNTIME_MANIFEST"]
        ),
        "execution_report": _identity(
            "validation/execution_report.json", artifact_bytes["EXECUTION_REPORT"]
        ),
        "candidate_artifact_root_sha256": candidate_root,
        "candidate_status": (
            "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED"
            if blocked
            else "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW"
        ),
        "block_reason_codes": ["CONTROL-FAILED"] if blocked else [],
        "terminal": True,
    }
    _put_document(documents, artifact_bytes, "TERMINAL_ENVELOPE", terminal_doc)
    schema_names["TERMINAL_ENVELOPE"] = "terminal_envelope"

    review_rows = _independent_review_consumer_rows()
    review_ids = [row["consumer_id"] for row in review_rows]
    review_runtime_ids = [
        row["consumer_id"] for row in review_rows if row["runtime_required"]
    ]
    review_delta_rows = _independent_review_baseline_delta_rows(review_rows)
    review_all_root = _identity_root(review_ids, review=True)
    review_runtime_root = _runtime_identity_root(review_runtime_ids, review=True)
    review_inventory_doc = {
        "schema_id": "LOOP_CONTROL_INDEPENDENT_REVIEW_CONSUMER_INVENTORY_v2",
        "inventory_origin": "INDEPENDENT_REVIEW_GIT_OBJECT_RESCAN",
        "algorithm_id": "LOOP_CONTROL_CONSUMER_DISCOVERY_CALLSITE_v2",
        "scanner_implementation_id": (
            "INDEPENDENT_REVIEW_FULL_TREE_CAT_FILE_SCANNER_v2"
        ),
        "source_commit": SOURCE_COMMIT,
        "source_tree": SOURCE_TREE,
        "consumers": review_rows,
        "consumer_identity_count": len(review_rows),
        "consumer_identity_root_sha256": review_all_root,
        "runtime_required_count": len(review_runtime_ids),
        "runtime_required_identity_root_sha256": review_runtime_root,
        "nonruntime_count": len(review_rows) - len(review_runtime_ids),
        "unique_path_count": len({row["path"] for row in review_rows}),
        "baseline_delta_rows": review_delta_rows,
        "baseline_delta_root_sha256": _delta_root(
            review_delta_rows, review=True
        ),
    }
    _put_document(
        documents,
        artifact_bytes,
        "INDEPENDENT_REVIEW_CONSUMER_INVENTORY",
        review_inventory_doc,
    )
    schema_names["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"] = (
        "independent_review_consumer_inventory"
    )
    review_doc = {
        "schema_id": "LOOP_CONTROL_STAGE_A_INDEPENDENT_REVIEW_BINDING_v2",
        "terminal_envelope": _identity(
            "manifests/terminal_envelope.json", artifact_bytes["TERMINAL_ENVELOPE"]
        ),
        "review_inventory": _identity(
            "review/consumer_inventory.json",
            artifact_bytes["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"],
        ),
        "execution_inventory_root_sha256": all_root,
        "independent_rescan_root_sha256": review_all_root,
        "independent_rescan_performed": True,
        "inventory_source": "INDEPENDENT_GIT_OBJECT_RESCAN",
        "decision": "B_BLOCKED" if blocked else "ACCEPT_STAGE_A_CANDIDATE_ONLY",
        "stage_b_authorized": False,
    }
    _put_document(documents, artifact_bytes, "INDEPENDENT_REVIEW", review_doc)
    schema_names["INDEPENDENT_REVIEW"] = "independent_review_binding"

    artifact_generation_ledger = list(artifact_bytes)
    generation_ledger = _full_generation_ledger()
    return {
        "artifact_generation_ledger": artifact_generation_ledger,
        "artifact_bytes": artifact_bytes,
        "branch": branch,
        "documents": documents,
        "execution_commit": SOURCE_COMMIT,
        "execution_tree": SOURCE_TREE,
        "generation_ledger": generation_ledger,
        "history_record_count": len(history_witness["records"]),
        "history_shard_count": len(history_witness["members"]),
        "history_shard_members": dict(history_witness["members"]),
        "operation_result_bytes": operation_result_bytes,
        "paths": paths,
        "schema_names": schema_names,
        "trace_documents": trace_documents,
    }


def _assert_identity(
    identity: dict[str, Any], path: str, raw: bytes, error_code: str
) -> None:
    if identity != _identity(path, raw):
        raise V2PreparationError(error_code)


def _rebind_candidate_map(fixture: dict[str, Any]) -> None:
    document = fixture["documents"]["CONSUMER_MAP"]
    rows = document["consumers"]
    ids = [row["consumer_id"] for row in rows]
    runtime_ids = [row["consumer_id"] for row in rows if row["runtime_required"]]
    document["consumer_identity_count"] = len(rows)
    document["consumer_identity_root_sha256"] = _identity_root(ids)
    document["runtime_required_count"] = len(runtime_ids)
    document["runtime_required_identity_root_sha256"] = _runtime_identity_root(
        runtime_ids
    )
    document["nonruntime_count"] = len(rows) - len(runtime_ids)
    fixture["artifact_bytes"]["CONSUMER_MAP"] = canonical_json_bytes(document)


def _rebind_trace(fixture: dict[str, Any]) -> None:
    trace = fixture["trace_documents"]
    fixture["artifact_bytes"]["RUNTIME_TRACE"] = b"".join(
        compact_json_bytes(event) + b"\n" for event in trace
    )
    manifest = fixture["documents"]["RUNTIME_TRACE_MANIFEST"]
    ids = [event["consumer_id"] for event in trace]
    manifest["runtime_trace"] = _identity(
        "traces/runtime_trace.jsonl", fixture["artifact_bytes"]["RUNTIME_TRACE"]
    )
    manifest["traced_consumer_identity_root_sha256"] = _runtime_identity_root(ids)
    manifest["event_count"] = len(trace)
    manifest["runtime_required_count"] = len(ids)
    manifest["unmatched_trace_count"] = 0
    manifest["unobserved_runtime_required_count"] = 0
    fixture["artifact_bytes"]["RUNTIME_TRACE_MANIFEST"] = canonical_json_bytes(
        manifest
    )


def validate_cross_document_lifecycle(fixture: dict[str, Any]) -> None:
    """Validate actual fixture documents, bytes, hashes, sets, and order."""

    branch = fixture["branch"]
    if branch not in {"COMPLETE", "POST_GENERATION_BLOCKED"}:
        raise V2PreparationError("V2-E-LIFECYCLE-BRANCH-MISMATCH")
    if fixture.get("candidate_expected_consumer_count") is not None:
        raise V2PreparationError("V2-E-STALE-CONSUMER-COUNT")

    schemas = build_runtime_schemas()
    validate_schema_graph(schemas, REVIEWED_EDGE_TABLE)
    documents = fixture["documents"]
    artifact_bytes = fixture["artifact_bytes"]
    if documents["PREFLIGHT_CONSUMER_INVENTORY"]["inventory_origin"] != (
        "REPOSITORY_GIT_OBJECT_SCAN"
    ):
        raise V2PreparationError("V2-E-CONSUMER-INVENTORY-TRUST-ROOT")
    if documents["CONSUMER_MAP"]["inventory_origin"] != (
        "EXACT_PREFLIGHT_REPOSITORY_PROJECTION"
    ):
        raise V2PreparationError("V2-E-CONSUMER-INVENTORY-TRUST-ROOT")
    if documents["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"]["inventory_origin"] != (
        "INDEPENDENT_REVIEW_GIT_OBJECT_RESCAN"
    ) or documents["INDEPENDENT_REVIEW"]["inventory_source"] != (
        "INDEPENDENT_GIT_OBJECT_RESCAN"
    ):
        raise V2PreparationError("V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED")
    for artifact_type, document in documents.items():
        Draft202012Validator(
            schemas[fixture["schema_names"][artifact_type]]
        ).validate(document)

    ledger = fixture["generation_ledger"]
    if len(ledger) != len(set(ledger)):
        raise V2PreparationError("V2-E-REQUIRED-NODE-CARDINALITY")
    ordinals = {artifact: ARTIFACT_PHASES[artifact][1] for artifact in ledger}
    if [ordinals[artifact] for artifact in ledger] != sorted(ordinals.values()):
        raise V2PreparationError("V2-E-SCHEMA-GENERATION-ORDER-MISMATCH")

    inventory = documents["PREFLIGHT_CONSUMER_INVENTORY"]
    preflight_rows = inventory["consumers"]
    if preflight_rows != _consumer_rows():
        return "V2-E-PREFLIGHT-REPOSITORY-RESCAN-MISMATCH"
    preflight_ids = [row["consumer_id"] for row in preflight_rows]
    if len(preflight_ids) != len(set(preflight_ids)):
        raise V2PreparationError("V2-E-DUPLICATE-CONSUMER-ID")
    if any(_consumer_id(row) != row["consumer_id"] for row in preflight_rows):
        raise V2PreparationError("V2-E-CONSUMER-IDENTITY-MISMATCH")
    runtime_ids = [
        row["consumer_id"] for row in preflight_rows if row["runtime_required"]
    ]
    expected_delta = _execution_baseline_delta_rows(preflight_rows)
    if sorted(
        inventory["baseline_delta_rows"],
        key=lambda row: (row["path"], row["classification"]),
    ) != expected_delta:
        raise V2PreparationError("V2-E-BASELINE-CHANGE-UNCLASSIFIED")
    if inventory["baseline_delta_root_sha256"] != _delta_root(expected_delta):
        raise V2PreparationError("V2-E-BASELINE-CHANGE-UNCLASSIFIED")
    if (
        inventory["consumer_identity_count"] != len(preflight_rows)
        or inventory["consumer_identity_root_sha256"] != _identity_root(preflight_ids)
        or inventory["runtime_required_count"] != len(runtime_ids)
        or inventory["runtime_required_identity_root_sha256"]
        != _runtime_identity_root(runtime_ids)
        or inventory["nonruntime_count"] != len(preflight_rows) - len(runtime_ids)
    ):
        raise V2PreparationError("V2-E-PREFLIGHT-INVENTORY-INTERNAL-MISMATCH")

    attestation = documents["EXECUTION_PREFLIGHT_ATTESTATION"]
    _assert_identity(
        attestation["consumer_inventory"],
        "preflight/consumer_inventory.json",
        artifact_bytes["PREFLIGHT_CONSUMER_INVENTORY"],
        "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH",
    )
    if (
        attestation["consumer_identity_count"] != len(preflight_rows)
        or attestation["consumer_identity_root_sha256"] != _identity_root(preflight_ids)
        or attestation["runtime_required_count"] != len(runtime_ids)
        or attestation["runtime_required_identity_root_sha256"]
        != _runtime_identity_root(runtime_ids)
        or attestation["candidate_supplied_inventory_used"]
    ):
        raise V2PreparationError("V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH")
    source = documents["SOURCE_MANIFEST"]
    _assert_identity(
        source["preflight_attestation"],
        "manifests/preflight_attestation.json",
        artifact_bytes["EXECUTION_PREFLIGHT_ATTESTATION"],
        "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH",
    )

    candidate_map = documents["CONSUMER_MAP"]
    candidate_rows = candidate_map["consumers"]
    candidate_ids = [row["consumer_id"] for row in candidate_rows]
    if len(candidate_ids) != len(set(candidate_ids)):
        raise V2PreparationError("V2-E-DUPLICATE-CONSUMER-ID")
    if any(_consumer_id(row) != row["consumer_id"] for row in candidate_rows):
        raise V2PreparationError("V2-E-CONSUMER-IDENTITY-MISMATCH")
    candidate_runtime_ids = [
        row["consumer_id"] for row in candidate_rows if row["runtime_required"]
    ]
    if (
        candidate_map["consumer_identity_count"] != len(candidate_rows)
        or candidate_map["consumer_identity_root_sha256"] != _identity_root(candidate_ids)
        or candidate_map["runtime_required_count"] != len(candidate_runtime_ids)
        or candidate_map["runtime_required_identity_root_sha256"]
        != _runtime_identity_root(candidate_runtime_ids)
    ):
        raise V2PreparationError("V2-E-CONSUMER-MAP-INTERNAL-MISMATCH")
    trace_ids = [event["consumer_id"] for event in fixture["trace_documents"]]
    if set(candidate_ids) < set(preflight_ids) and set(trace_ids) == set(
        candidate_runtime_ids
    ):
        raise V2PreparationError("V2-E-CONSUMER-LOCAL-REBIND")
    preflight_by_id = {row["consumer_id"]: row for row in preflight_rows}
    candidate_by_id = {row["consumer_id"]: row for row in candidate_rows}
    for consumer_id in set(preflight_by_id) & set(candidate_by_id):
        if candidate_by_id[consumer_id]["runtime_required"] != preflight_by_id[
            consumer_id
        ]["runtime_required"]:
            raise V2PreparationError("V2-E-RUNTIME-REQUIRED-MISCLASSIFIED")
    omitted = set(preflight_ids) - set(candidate_ids)
    invented = set(candidate_ids) - set(preflight_ids)
    if omitted and len(candidate_ids) == 1:
        raise V2PreparationError("V2-E-CONSUMER-INVENTORY-INCOMPLETE")
    if omitted:
        raise V2PreparationError("V2-E-FRESH-CONSUMER-OMITTED")
    if invented:
        raise V2PreparationError("V2-E-CONSUMER-INVENTED")
    _assert_identity(
        candidate_map["preflight_inventory"],
        "preflight/consumer_inventory.json",
        artifact_bytes["PREFLIGHT_CONSUMER_INVENTORY"],
        "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH",
    )

    if len(trace_ids) != len(set(trace_ids)) or set(trace_ids) != set(runtime_ids):
        raise V2PreparationError("V2-E-RUNTIME-TRACE-INCOMPLETE")
    for event in fixture["trace_documents"]:
        row = preflight_by_id.get(event["consumer_id"])
        if row is None or (
            event["consumer_path"],
            event["consumer_source_sha256"],
            event["operation_class"],
        ) != (row["path"], row["source_sha256"], row["operation_class"]):
            raise V2PreparationError("V2-E-RUNTIME-TRACE-UNMATCHED")
    trace_manifest = documents["RUNTIME_TRACE_MANIFEST"]
    _assert_identity(
        trace_manifest["consumer_map"],
        "consumers/consumer_map.json",
        artifact_bytes["CONSUMER_MAP"],
        "V2-E-CONSUMER-TRACE-BINDING-MISMATCH",
    )
    _assert_identity(
        trace_manifest["runtime_trace"],
        "traces/runtime_trace.jsonl",
        artifact_bytes["RUNTIME_TRACE"],
        "V2-E-CONSUMER-TRACE-BINDING-MISMATCH",
    )
    if (
        trace_manifest["event_count"] != len(trace_ids)
        or trace_manifest["runtime_required_count"] != len(runtime_ids)
        or trace_manifest["runtime_required_identity_root_sha256"]
        != _runtime_identity_root(runtime_ids)
        or trace_manifest["unmatched_trace_count"] != 0
        or trace_manifest["unobserved_runtime_required_count"] != 0
    ):
        raise V2PreparationError("V2-E-RUNTIME-TRACE-INCOMPLETE")

    runtime = documents["RUNTIME_MANIFEST"]
    candidate_rows_by_type = {
        row["artifact_type"]: row for row in runtime["candidate_artifacts"]
    }
    if len(candidate_rows_by_type) != len(runtime["candidate_artifacts"]):
        raise V2PreparationError("V2-E-RUNTIME-CANDIDATE-DUPLICATE")
    for artifact_type, row in candidate_rows_by_type.items():
        if row != _candidate_row(
            artifact_type, fixture["paths"][artifact_type], artifact_bytes[artifact_type]
        ):
            raise V2PreparationError("V2-E-RUNTIME-CANDIDATE-BINDING-MISMATCH")
    if runtime["candidate_artifact_root_sha256"] != _artifact_root(
        runtime["candidate_artifacts"],
        b"LOOP_CONTROL_ALL_CANDIDATE_ARTIFACT_ROOT_v2",
    ):
        raise V2PreparationError("V2-E-RUNTIME-CANDIDATE-BINDING-MISMATCH")
    report = documents["EXECUTION_REPORT"]
    _assert_identity(
        report["runtime_manifest"],
        "manifests/runtime_manifest.json",
        artifact_bytes["RUNTIME_MANIFEST"],
        "V2-E-REPORT-RUNTIME-BINDING-MISMATCH",
    )
    terminal = documents["TERMINAL_ENVELOPE"]
    _assert_identity(
        terminal["runtime_manifest"],
        "manifests/runtime_manifest.json",
        artifact_bytes["RUNTIME_MANIFEST"],
        "V2-E-TERMINAL-RUNTIME-BINDING-MISMATCH",
    )
    _assert_identity(
        terminal["execution_report"],
        "validation/execution_report.json",
        artifact_bytes["EXECUTION_REPORT"],
        "V2-E-TERMINAL-REPORT-BINDING-MISMATCH",
    )

    review_inventory = documents["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"]
    review_ids = [row["consumer_id"] for row in review_inventory["consumers"]]
    review_runtime_ids = [
        row["consumer_id"]
        for row in review_inventory["consumers"]
        if row["runtime_required"]
    ]
    if set(review_ids) != set(preflight_ids) or set(review_runtime_ids) != set(
        runtime_ids
    ):
        raise V2PreparationError("V2-E-REVIEW-CONSUMER-RESCAN-MISMATCH")
    review = documents["INDEPENDENT_REVIEW"]
    _assert_identity(
        review["terminal_envelope"],
        "manifests/terminal_envelope.json",
        artifact_bytes["TERMINAL_ENVELOPE"],
        "V2-E-REVIEW-TERMINAL-BINDING-MISMATCH",
    )
    _assert_identity(
        review["review_inventory"],
        "review/consumer_inventory.json",
        artifact_bytes["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"],
        "V2-E-REVIEW-CONSUMER-RESCAN-MISMATCH",
    )
    blocked = branch == "POST_GENERATION_BLOCKED"
    if blocked:
        if not (
            runtime["status"] == "B_BLOCKED_CANDIDATE_PRESERVED"
            and report["status"] == "B_BLOCKED_CANDIDATE_PRESERVED"
            and terminal["candidate_status"] == "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED"
            and review["decision"] == "B_BLOCKED"
        ):
            raise V2PreparationError("V2-E-POST-GENERATION-BLOCKED-CHAIN-UNSATISFIABLE")
    elif not (
        runtime["status"] == "CANDIDATE_COMPLETE"
        and report["status"] == "STAGE_A_CANDIDATE_COMPLETE"
        and terminal["candidate_status"]
        == "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW"
        and review["decision"] == "ACCEPT_STAGE_A_CANDIDATE_ONLY"
    ):
        raise V2PreparationError("V2-E-COMPLETE-CHAIN-UNSATISFIABLE")


def mutate_cross_document_fixture(fixture: dict[str, Any], mutation: str) -> None:
    if mutation == "consumer_map_truncated_to_one_row":
        fixture["documents"]["CONSUMER_MAP"]["consumers"] = fixture["documents"][
            "CONSUMER_MAP"
        ]["consumers"][:1]
        _rebind_candidate_map(fixture)
    elif mutation == "trace_truncated_to_match_consumer_map":
        fixture["trace_documents"] = fixture["trace_documents"][:1]
        _rebind_trace(fixture)
    elif mutation == "consumer_map_and_trace_locally_rebound":
        fixture["documents"]["CONSUMER_MAP"]["consumers"] = [
            next(
                row
                for row in fixture["documents"]["CONSUMER_MAP"]["consumers"]
                if row["runtime_required"]
            )
        ]
        _rebind_candidate_map(fixture)
        retained = {
            row["consumer_id"]
            for row in fixture["documents"]["CONSUMER_MAP"]["consumers"]
            if row["runtime_required"]
        }
        fixture["trace_documents"] = [
            event
            for event in fixture["trace_documents"]
            if event["consumer_id"] in retained
        ]
        _rebind_trace(fixture)
    elif mutation == "stale_historical_count_treated_as_current_truth":
        fixture["candidate_expected_consumer_count"] = 520
    elif mutation == "fresh_consumer_omitted":
        fixture["documents"]["CONSUMER_MAP"]["consumers"].pop()
        _rebind_candidate_map(fixture)
    elif mutation == "invented_consumer_inserted":
        invented = deepcopy(fixture["documents"]["CONSUMER_MAP"]["consumers"][0])
        invented["path"] = "invented/consumer.py"
        invented["consumer_id"] = _consumer_id(invented)
        fixture["documents"]["CONSUMER_MAP"]["consumers"].append(invented)
        _rebind_candidate_map(fixture)
    elif mutation == "runtime_required_consumer_classified_nonruntime":
        next(
            row
            for row in fixture["documents"]["CONSUMER_MAP"]["consumers"]
            if row["runtime_required"]
        )["runtime_required"] = False
        _rebind_candidate_map(fixture)
    elif mutation == "baseline_path_changed_without_delta_classification":
        inventory = fixture["documents"]["PREFLIGHT_CONSUMER_INVENTORY"]
        inventory["baseline_delta_rows"] = [
            row for row in inventory["baseline_delta_rows"] if row["classification"] != "CHANGED"
        ]
        inventory["baseline_delta_root_sha256"] = _delta_root(
            inventory["baseline_delta_rows"]
        )
        fixture["artifact_bytes"]["PREFLIGHT_CONSUMER_INVENTORY"] = canonical_json_bytes(
            inventory
        )
    elif mutation == "preflight_inventory_altered_after_source_manifest_creation":
        inventory = fixture["documents"]["PREFLIGHT_CONSUMER_INVENTORY"]
        inventory["unique_path_count"] += 1
        fixture["artifact_bytes"]["PREFLIGHT_CONSUMER_INVENTORY"] = canonical_json_bytes(
            inventory
        )
    elif mutation == "consumer_inventory_derived_from_candidate":
        fixture["documents"]["PREFLIGHT_CONSUMER_INVENTORY"]["inventory_origin"] = (
            "CANDIDATE_CONSUMER_MAP"
        )
        _rebind_after_inventory(fixture)
    elif mutation == "review_trusts_execution_inventory_without_rescan":
        fixture["documents"]["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"][
            "inventory_origin"
        ] = "REPOSITORY_GIT_OBJECT_SCAN"
        fixture["documents"]["INDEPENDENT_REVIEW"]["inventory_source"] = (
            "EXECUTION_PREFLIGHT_ATTESTATION"
        )
    else:
        raise ValueError(f"not a cross-document inventory mutation: {mutation}")


def build_preflight_blocked_fixture() -> dict[str, Any]:
    document = {
        "schema_id": "LOOP_CONTROL_STAGE_A_PREFLIGHT_DIAGNOSTIC_v2",
        "classification": "blocked_preflight_consumer_rescan_failure",
        "error_code": "V2-E-CONSUMER-RESCAN-FAILURE",
        "message": "bounded preflight diagnostic",
        "exit_code": 2,
        "candidate_set_created": False,
        "prototype_run_root_created": False,
        "controls_observed": 0,
    }
    return {
        "candidate_artifacts": [],
        "diagnostic": document,
        "exit_code": 2,
        "prototype_run_root_created": False,
    }


def validate_preflight_blocked_fixture(fixture: dict[str, Any]) -> None:
    Draft202012Validator(build_runtime_schemas()["preflight_diagnostic"]).validate(
        fixture["diagnostic"]
    )
    if not (
        fixture["exit_code"] != 0
        and not fixture["prototype_run_root_created"]
        and not fixture["candidate_artifacts"]
    ):
        raise V2PreparationError("V2-E-PREFLIGHT-BRANCH-UNSATISFIABLE")


def _identity_matches(identity: dict[str, Any], raw: bytes) -> bool:
    return identity.get("sha256") == sha256(raw) and identity.get("size_bytes") == len(raw)


def _refresh_document_bytes(fixture: dict[str, Any], artifact_type: str) -> None:
    fixture["artifact_bytes"][artifact_type] = canonical_json_bytes(
        fixture["documents"][artifact_type]
    )


def _trace_ids(fixture: dict[str, Any]) -> set[str]:
    return {event["consumer_id"] for event in fixture["trace_documents"]}


def _derived_runtime_required(row: dict[str, Any]) -> bool:
    return row["consumer_category"] in RUNTIME_REQUIRED_CATEGORIES


def _instance_hash_bindings(
    instance: Any, schema: dict[str, Any], path: str = ""
) -> list[tuple[str, str, str]]:
    observed: set[tuple[str, str, str]] = set()

    def walk(value: Any, shape: Any, pointer: str) -> None:
        if not isinstance(shape, dict):
            return
        properties = shape.get("properties")
        if isinstance(value, dict) and isinstance(properties, dict):
            for name, child_schema in properties.items():
                if name not in value:
                    continue
                child_path = f"{pointer}/{_escape_pointer(name)}"
                annotation = (
                    child_schema.get("x-toe-hash-edge")
                    if isinstance(child_schema, dict)
                    else None
                )
                if isinstance(annotation, dict) and isinstance(value[name], str):
                    target = annotation["referenced_artifact_type"]
                    if target == "DYNAMIC_CANDIDATE_ARTIFACT":
                        target = value.get("artifact_type", target)
                    observed.add(
                        (
                            child_path,
                            target,
                            value[name],
                        )
                    )
                walk(value[name], child_schema, child_path)
        if isinstance(value, list) and isinstance(shape.get("items"), dict):
            for child in value:
                walk(child, shape["items"], f"{pointer}/*")
        for keyword in ("oneOf", "allOf", "anyOf"):
            alternatives = shape.get(keyword)
            if isinstance(alternatives, list):
                for child_schema in alternatives:
                    walk(value, child_schema, pointer)

    walk(instance, schema, path)
    return sorted(observed)


def _required_instance_edge_keys(
    edge_table: list[dict[str, Any]], branch: str
) -> set[tuple[str, str, str]]:
    applicability_key = {
        "COMPLETE": "complete_path_applicability",
        "POST_GENERATION_BLOCKED": "blocked_path_applicability",
    }.get(branch)
    if applicability_key is None:
        raise V2PreparationError("V2-E-LIFECYCLE-BRANCH-MISMATCH")
    return {
        (
            row["containing_artifact_type"],
            row["schema_field_path"],
            row["referenced_artifact_type"],
        )
        for row in edge_table
        if row[applicability_key] == "REQUIRED"
    }


def validate_lifecycle_fixture(fixture: dict[str, Any]) -> str | None:
    schemas = build_runtime_schemas()
    documents = fixture["documents"]
    raw = fixture["artifact_bytes"]
    branch = fixture["branch"]

    # The predecessor controls are evaluated through this same executable
    # validator.  Classify their structural defects before closed-schema
    # validation would collapse them into a generic diagnostic.
    source_document = documents["SOURCE_MANIFEST"]
    runtime_document = documents["RUNTIME_MANIFEST"]
    report_document = documents["EXECUTION_REPORT"]
    terminal_document = documents["TERMINAL_ENVELOPE"]
    review_document = documents["INDEPENDENT_REVIEW"]
    if "runtime_manifest" in source_document:
        return "V1-E-UNSATISFIABLE-ARTIFACT-MANIFEST-CYCLE"
    if "source_manifest" not in runtime_document:
        return "V1-E-RUNTIME-SOURCE-MANIFEST-BINDING-MISSING"
    if "terminal_envelope" in runtime_document:
        return "V1-E-HASH-DAG-FORWARD-REFERENCE"
    if "self_sha256" in terminal_document:
        return "V1-E-TERMINAL-ENVELOPE-SELF-REFERENCE"
    if "terminal_envelope" in report_document:
        return "V1-E-EXECUTION-TERMINAL-CYCLE"
    if {"temporary_path", "captured_at_utc"}.intersection(source_document):
        return "V1-E-SOURCE-MANIFEST-NONDETERMINISTIC-FIELD"
    if "terminal_envelope" not in review_document:
        return "V1-E-REVIEW-MISSING-TERMINAL-ENVELOPE"
    ledger = fixture["generation_ledger"]
    if (
        "RUNTIME_MANIFEST" in ledger
        and "VALIDATION_REPORT" in ledger
        and ledger.index("RUNTIME_MANIFEST") < ledger.index("VALIDATION_REPORT")
    ):
        return "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET"
    if terminal_document.get("run_id") != report_document.get("run_id"):
        return "V1-E-TERMINAL-CROSS-RUN-BINDING"
    if source_document.get("source_registry", {}).get("sha256") != REGISTRY_SHA256:
        return "V1-E-EXTERNAL-TRUST-ROOT-REBIND"
    if not _identity_matches(
        runtime_document["source_manifest"], raw["SOURCE_MANIFEST"]
    ):
        return "V1-E-RUNTIME-SOURCE-MANIFEST-BINDING-MISMATCH"

    # Trust-root errors are classified before ordinary schema diagnostics so
    # prohibited candidate/review origins receive their permanent exact code.
    if documents["PREFLIGHT_CONSUMER_INVENTORY"].get("inventory_origin") != (
        "REPOSITORY_GIT_OBJECT_SCAN"
    ) or documents["EXECUTION_PREFLIGHT_ATTESTATION"].get(
        "candidate_supplied_inventory_used"
    ):
        return "V2-E-CONSUMER-INVENTORY-TRUST-ROOT"
    if (
        not documents["INDEPENDENT_REVIEW"].get("independent_rescan_performed")
        or documents["INDEPENDENT_REVIEW"].get("inventory_source")
        != "INDEPENDENT_GIT_OBJECT_RESCAN"
        or documents["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"].get(
            "scanner_implementation_id"
        )
        != "INDEPENDENT_REVIEW_FULL_TREE_CAT_FILE_SCANNER_v2"
    ):
        return "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"

    # Actual bytes must be canonical schema-valid documents, not facade flags.
    try:
        for artifact_type, schema_name in fixture["schema_names"].items():
            Draft202012Validator(schemas[schema_name]).validate(
                documents[artifact_type]
            )
            expected_bytes = (
                _history_witness()["set_bytes"]
                if artifact_type == "HISTORY_SHARD"
                else canonical_json_bytes(documents[artifact_type])
            )
            if raw[artifact_type] != expected_bytes:
                return "V2-E-DOCUMENT-CANONICAL-BYTES-MISMATCH"
        for event in fixture["trace_documents"]:
            Draft202012Validator(schemas["runtime_trace_event"]).validate(event)
    except Exception:
        return "V2-E-DOCUMENT-SCHEMA-MISMATCH"
    realized_instance_edges: set[tuple[str, str, str]] = set()
    observed_instance_hashes: list[tuple[str, str, str, str]] = []
    for artifact_type, schema_name in fixture["schema_names"].items():
        for field_path, target, observed_sha in _instance_hash_bindings(
            documents[artifact_type], schemas[schema_name]
        ):
            realized_instance_edges.add((artifact_type, field_path, target))
            observed_instance_hashes.append(
                (artifact_type, field_path, target, observed_sha)
            )
            if target == "HISTORY_SHARD":
                valid_shard_hashes = {
                    sha256(member_raw)
                    for member_raw in fixture["history_shard_members"].values()
                }
                if observed_sha not in valid_shard_hashes:
                    return "V2-E-INSTANCE-HASH-GRAPH-MISMATCH"
            elif target in raw and observed_sha != sha256(raw[target]):
                if target in {
                    "PREFLIGHT_CONSUMER_INVENTORY",
                    "EXECUTION_PREFLIGHT_ATTESTATION",
                }:
                    return "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH"
                return "V2-E-INSTANCE-HASH-GRAPH-MISMATCH"
    for event in fixture["trace_documents"]:
        for field_path, target, observed_sha in _instance_hash_bindings(
            event, schemas["runtime_trace_event"]
        ):
            realized_instance_edges.add(("RUNTIME_TRACE", field_path, target))
            observed_instance_hashes.append(
                ("RUNTIME_TRACE", field_path, target, observed_sha)
            )
    reviewed_instance_edges = {
        (
            row["containing_artifact_type"],
            row["schema_field_path"],
            row["referenced_artifact_type"],
        )
        for row in REVIEWED_EDGE_TABLE
    }
    required_instance_edges = _required_instance_edge_keys(
        REVIEWED_EDGE_TABLE, branch
    )
    if (
        realized_instance_edges - reviewed_instance_edges
        or required_instance_edges - realized_instance_edges
    ):
        return "V2-E-INSTANCE-HASH-GRAPH-MISMATCH"

    inventory = documents["PREFLIGHT_CONSUMER_INVENTORY"]
    attestation = documents["EXECUTION_PREFLIGHT_ATTESTATION"]
    source = documents["SOURCE_MANIFEST"]
    candidate_map = documents["CONSUMER_MAP"]
    trace_manifest = documents["RUNTIME_TRACE_MANIFEST"]
    runtime = documents["RUNTIME_MANIFEST"]
    report = documents["EXECUTION_REPORT"]
    terminal = documents["TERMINAL_ENVELOPE"]
    current_projection = documents["CURRENT_PROJECTION"]
    validation_report = documents["VALIDATION_REPORT"]
    control_evidence = documents["CONTROL_EVIDENCE"]
    rollback_inventory = documents["ROLLBACK_INVENTORY"]
    trust_anchors = documents["REVIEWED_TRUST_ANCHORS"]
    review_inventory = documents["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"]
    review = documents["INDEPENDENT_REVIEW"]

    if (
        fixture.get("execution_commit") != SOURCE_COMMIT
        or fixture.get("execution_tree") != SOURCE_TREE
        or inventory.get("source_commit") != SOURCE_COMMIT
        or inventory.get("source_tree") != SOURCE_TREE
        or attestation.get("source_commit") != SOURCE_COMMIT
        or attestation.get("source_tree") != SOURCE_TREE
        or source.get("source_commit") != SOURCE_COMMIT
    ):
        return "V2-E-PREFLIGHT-SOURCE-COMMIT-MISMATCH"

    expected_external = _lifecycle_model_external_identities(schemas)
    expected_contract_identity = expected_external["V2_CONTRACT"]
    expected_schema_identity = expected_external["V2_SCHEMA_BUNDLE"]
    expected_protocol_identity = expected_external["EXECUTION_PROTOCOL"]
    expected_implementation_identity = expected_external[
        "AUTHORIZED_IMPLEMENTATION"
    ]
    expected_review_identity = expected_external[
        "ACCEPTED_V2_INDEPENDENT_REVIEW"
    ]
    expected_registry_identity = expected_external["SOURCE_REGISTRY"]
    if (
        attestation["reviewed_contract"] != expected_contract_identity
        or source["reviewed_contract"] != expected_contract_identity
        or attestation["schema_bundle"] != expected_schema_identity
        or source["schema_bundle"] != expected_schema_identity
        or trust_anchors["schema_bundle"] != expected_schema_identity
        or attestation["protocol_bundle"] != expected_protocol_identity
        or source["protocol_bundle"] != expected_protocol_identity
        or trust_anchors["protocol_bundle"] != expected_protocol_identity
        or attestation["implementation_inventory"]
        != expected_implementation_identity
        or source["implementation_inventory"]
        != expected_implementation_identity
        or source["accepted_contract_review"] != expected_review_identity
        or trust_anchors["accepted_contract_review"]
        != expected_review_identity
        or attestation["source_registry"] != expected_registry_identity
        or source["source_registry"] != expected_registry_identity
        or trust_anchors["source_registry"] != expected_registry_identity
        or attestation["reviewed_contract"] != source["reviewed_contract"]
        or attestation["schema_bundle"] != source["schema_bundle"]
        or attestation["schema_bundle"] != trust_anchors["schema_bundle"]
        or attestation["protocol_bundle"] != source["protocol_bundle"]
        or attestation["protocol_bundle"] != trust_anchors["protocol_bundle"]
        or attestation["implementation_inventory"]
        != source["implementation_inventory"]
        or source["accepted_contract_review"]
        != trust_anchors["accepted_contract_review"]
        or source["source_registry"] != trust_anchors["source_registry"]
        or current_projection["maintenance_authority"]["evidence"]
        != {
            "path": MAINTENANCE_AUTHORITY_REL,
            "sha256": EXPECTED_INPUTS[MAINTENANCE_AUTHORITY_REL][0],
        }
        or current_projection["scientific_authority"]
        ["authority_commitment_sha256"]
        != AUTHORITY_COMMITMENT_SHA256
        or trust_anchors["authority_commitment_sha256"]
        != AUTHORITY_COMMITMENT_SHA256
        or documents["HISTORY_INDEX"]["record_accounting"]
        ["authority_commitment_sha256"]
        != AUTHORITY_COMMITMENT_SHA256
        or documents["CUSTODY_MANIFEST"]["generation_provenance"]
        ["generator_sha256"]
        != expected_implementation_identity["sha256"]
        or documents["LEGACY_RECONSTRUCTION"]["validator_identity"]
        ["sha256"]
        != expected_implementation_identity["sha256"]
        or source["execution_command"] != EXECUTION_COMMAND
        or runtime["execution_command"] != EXECUTION_COMMAND
    ):
        return "V2-E-EXTERNAL-TRUST-BINDING-MISMATCH"
    if (
        rollback_inventory["pre_run_inventory_sha256"]
        != _pre_run_inventory_root()
        or rollback_inventory["allowed_output_paths_sha256"]
        != _allowed_output_paths_root()
    ):
        return "V2-E-ROLLBACK-INVENTORY-ROOT-MISMATCH"

    if (
        inventory["inventory_origin"] != "REPOSITORY_GIT_OBJECT_SCAN"
        or inventory.get("scanner_implementation_id")
        != "EXECUTION_GIT_GREP_CAT_FILE_SCANNER_v2"
    ):
        return "V2-E-CONSUMER-INVENTORY-TRUST-ROOT"
    if attestation["candidate_supplied_inventory_used"]:
        return "V2-E-CONSUMER-INVENTORY-TRUST-ROOT"
    if not _identity_matches(
        attestation["consumer_inventory"], raw["PREFLIGHT_CONSUMER_INVENTORY"]
    ):
        return "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH"
    if not _identity_matches(
        source["preflight_attestation"], raw["EXECUTION_PREFLIGHT_ATTESTATION"]
    ):
        return "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH"
    if source["source_registry"]["sha256"] != REGISTRY_SHA256:
        return "V1-E-EXTERNAL-TRUST-ROOT-REBIND"

    registry_bytes = _source_registry_bytes()
    custody_payload = raw["CUSTODY_PAYLOAD"]
    try:
        reconstructed_registry = gzip.decompress(custody_payload)
    except (OSError, EOFError):
        return "V2-E-CUSTODY-RECONSTRUCTION-MISMATCH"
    custody_manifest = documents["CUSTODY_MANIFEST"]
    reconstruction = documents["LEGACY_RECONSTRUCTION"]
    source_identity = {
        "git_blob": EXPECTED_INPUTS[REGISTRY_REL][1],
        "path": REGISTRY_REL,
        "sha256": REGISTRY_SHA256,
        "size_bytes": len(registry_bytes),
        "source_commit": SOURCE_COMMIT,
    }
    if (
        reconstructed_registry != registry_bytes
        or custody_payload[:10]
        != b"\x1f\x8b\x08\x00\x00\x00\x00\x00\x02\xff"
        or custody_manifest["payload_identity"]
        != {
            "compressed_sha256": sha256(custody_payload),
            "compressed_size_bytes": len(custody_payload),
            "path": "custody/legacy.json.gz",
        }
        or custody_manifest["source_identity"] != source_identity
        or reconstruction["custody_payload_identity"]
        != _identity("custody/legacy.json.gz", custody_payload)
        or reconstruction["reconstruction_identity"]["sha256"]
        != sha256(reconstructed_registry)
        or reconstruction["reconstruction_identity"]["size_bytes"]
        != len(reconstructed_registry)
        or reconstruction["source_identity"] != source_identity
    ):
        return "V2-E-CUSTODY-RECONSTRUCTION-MISMATCH"

    expected_history = _history_witness(schemas["history_shard_record"])
    history_index = documents["HISTORY_INDEX"]
    if (
        fixture.get("history_record_count") != 4_691
        or fixture.get("history_shard_count")
        != len(expected_history["members"])
        or fixture.get("history_shard_members")
        != expected_history["members"]
        or documents["HISTORY_SHARD"]
        != expected_history["representative_record"]
        or raw["HISTORY_SHARD"] != expected_history["set_bytes"]
        or history_index["shards"] != expected_history["descriptors"]
        or history_index["shard_count"]
        != len(expected_history["descriptors"])
        or sum(
            descriptor["record_count"]
            for descriptor in history_index["shards"]
        )
        != history_index["record_accounting"]["total_record_count"]
    ):
        return "V2-E-HISTORY-SHARD-SEMANTIC-MISMATCH"

    preflight_rows = inventory["consumers"]
    preflight_ids = [row["consumer_id"] for row in preflight_rows]
    if len(preflight_ids) != len(set(preflight_ids)):
        return "V2-E-CONSUMER-ID-DUPLICATE"
    if any(row["consumer_id"] != _consumer_id(row) for row in preflight_rows):
        return "V2-E-CONSUMER-ID-MISMATCH"
    if any(row["runtime_required"] != _derived_runtime_required(row) for row in preflight_rows):
        return "V2-E-RUNTIME-REQUIRED-MISCLASSIFIED"
    runtime_ids = [row["consumer_id"] for row in preflight_rows if row["runtime_required"]]
    all_root = _identity_root(preflight_ids)
    runtime_root = _runtime_identity_root(runtime_ids)
    expected_counts = {
        "consumer_identity_count": len(preflight_rows),
        "runtime_required_count": len(runtime_ids),
        "nonruntime_count": len(preflight_rows) - len(runtime_ids),
    }
    for key, expected in expected_counts.items():
        if inventory[key] != expected or attestation[key] != expected or source.get(key, expected) != expected:
            return "V2-E-STALE-CONSUMER-COUNT"
    if inventory["unique_path_count"] != len({row["path"] for row in preflight_rows}):
        return "V2-E-STALE-CONSUMER-COUNT"
    if (
        inventory["consumer_identity_root_sha256"] != all_root
        or attestation["consumer_identity_root_sha256"] != all_root
        or source["consumer_identity_root_sha256"] != all_root
        or inventory["runtime_required_identity_root_sha256"] != runtime_root
        or attestation["runtime_required_identity_root_sha256"] != runtime_root
        or source["runtime_required_identity_root_sha256"] != runtime_root
    ):
        return "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH"
    expected_delta_rows = _execution_baseline_delta_rows(_consumer_rows())
    observed_delta_rows = sorted(
        inventory["baseline_delta_rows"],
        key=lambda row: (row["path"], row["classification"]),
    )
    expected_delta_root = _delta_root(expected_delta_rows)
    if (
        observed_delta_rows != expected_delta_rows
        or inventory["baseline_delta_root_sha256"] != expected_delta_root
        or attestation["baseline_delta_root_sha256"] != expected_delta_root
    ):
        return "V2-E-BASELINE-CHANGE-UNCLASSIFIED"
    if preflight_rows != _consumer_rows():
        return "V2-E-PREFLIGHT-REPOSITORY-RESCAN-MISMATCH"

    if not _identity_matches(candidate_map["source_manifest"], raw["SOURCE_MANIFEST"]):
        return "V1-E-RUNTIME-SOURCE-MANIFEST-BINDING-MISMATCH"
    if not _identity_matches(
        candidate_map["preflight_inventory"], raw["PREFLIGHT_CONSUMER_INVENTORY"]
    ):
        return "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH"
    candidate_rows = candidate_map["consumers"]
    candidate_ids = [row["consumer_id"] for row in candidate_rows]
    candidate_set = set(candidate_ids)
    preflight_set = set(preflight_ids)
    preflight_by_id = {row["consumer_id"]: row for row in preflight_rows}
    trace_set = _trace_ids(fixture)
    missing = preflight_set - candidate_set
    invented = candidate_set - preflight_set
    if invented:
        return "V2-E-CONSUMER-INVENTED"
    if missing:
        if len(candidate_rows) == 1:
            candidate_runtime = {
                row["consumer_id"] for row in candidate_rows if row["runtime_required"]
            }
            if trace_set == candidate_runtime:
                return "V2-E-CONSUMER-LOCAL-REBIND"
            return "V2-E-CONSUMER-INVENTORY-INCOMPLETE"
        return "V2-E-FRESH-CONSUMER-OMITTED"
    if len(candidate_ids) != len(set(candidate_ids)):
        return "V2-E-CONSUMER-ID-DUPLICATE"
    for candidate_row, preflight_row in zip(
        sorted(candidate_rows, key=lambda row: row["consumer_id"]),
        sorted(preflight_rows, key=lambda row: row["consumer_id"]),
        strict=True,
    ):
        if candidate_row != preflight_row:
            if candidate_row["runtime_required"] != preflight_row["runtime_required"]:
                return "V2-E-RUNTIME-REQUIRED-MISCLASSIFIED"
            return "V2-E-CONSUMER-INVENTORY-MISMATCH"
    if (
        candidate_map["consumer_identity_count"] != len(candidate_rows)
        or candidate_map["runtime_required_count"] != len(runtime_ids)
        or candidate_map["nonruntime_count"] != len(candidate_rows) - len(runtime_ids)
    ):
        return "V2-E-STALE-CONSUMER-COUNT"
    if (
        candidate_map["consumer_identity_root_sha256"] != all_root
        or candidate_map["runtime_required_identity_root_sha256"] != runtime_root
    ):
        return "V2-E-CONSUMER-LOCAL-REBIND"

    if not _identity_matches(trace_manifest["consumer_map"], raw["CONSUMER_MAP"]):
        return "V2-E-CONSUMER-LOCAL-REBIND"
    if not _identity_matches(trace_manifest["runtime_trace"], raw["RUNTIME_TRACE"]):
        return "V2-E-RUNTIME-TRACE-BINDING-MISMATCH"
    if trace_set - preflight_set:
        return "V2-E-RUNTIME-TRACE-UNMATCHED"
    required_set = set(runtime_ids)
    if (
        trace_set != required_set
        or len(fixture["trace_documents"]) != len(trace_set)
    ):
        return "V2-E-RUNTIME-TRACE-INCOMPLETE"
    expected_trace_bytes = b"".join(
        compact_json_bytes(event) + b"\n"
        for event in fixture["trace_documents"]
    )
    if raw["RUNTIME_TRACE"] != expected_trace_bytes:
        return "V2-E-RUNTIME-TRACE-BINDING-MISMATCH"
    expected_result_by_consumer = {
        row["consumer_id"]: sha256(_modeled_operation_result_bytes(row))
        for row in preflight_rows
        if row["runtime_required"]
    }
    if fixture.get("operation_result_bytes") != {
        row["consumer_id"]: _modeled_operation_result_bytes(row)
        for row in preflight_rows
        if row["runtime_required"]
    }:
        return "V2-E-RUNTIME-TRACE-PARITY-MISMATCH"
    for event in fixture["trace_documents"]:
        row = preflight_by_id.get(event["consumer_id"])
        if row is None or (
            event["consumer_path"],
            event["consumer_source_sha256"],
            event["operation_class"],
            event["write_attempted"],
        ) != (
            row["path"],
            row["source_sha256"],
            row["operation_class"],
            row["consumer_category"] == "WRITER",
        ):
            return "V2-E-RUNTIME-TRACE-UNMATCHED"
        if (
            event["trace_id"]
            != "lct2:" + sha256(event["consumer_id"].encode("utf-8"))
            or event["candidate_result_sha256"]
            != expected_result_by_consumer[event["consumer_id"]]
            or event["legacy_result_sha256"]
            != expected_result_by_consumer[event["consumer_id"]]
            or not event["semantic_parity"]
        ):
            return "V2-E-RUNTIME-TRACE-PARITY-MISMATCH"
    run_id = runtime["run_id"]
    if (
        trace_manifest["run_id"] != run_id
        or control_evidence["run_id"] != run_id
        or report["run_id"] != run_id
        or terminal["run_id"] != run_id
        or any(
            event["run_id"] != run_id
            for event in fixture["trace_documents"]
        )
    ):
        return "V2-E-RUN-CHAIN-MISMATCH"
    if (
        trace_manifest["event_count"] != len(fixture["trace_documents"])
        or trace_manifest["runtime_required_count"] != len(required_set)
        or trace_manifest["traced_consumer_identity_root_sha256"] != runtime_root
        or trace_manifest["runtime_required_identity_root_sha256"] != runtime_root
    ):
        return "V2-E-RUNTIME-TRACE-INCOMPLETE"

    expected_candidate_types = {
        "CUSTODY_PAYLOAD",
        "HISTORY_SHARD",
        "CONSUMER_MAP",
        "CUSTODY_MANIFEST",
        "LEGACY_RECONSTRUCTION",
        "HISTORY_INDEX",
        "CURRENT_PROJECTION",
        "RUNTIME_TRACE",
        "RUNTIME_TRACE_MANIFEST",
        "REVIEWED_TRUST_ANCHORS",
        "WRITER_PROBE",
        "ROLLBACK_INVENTORY",
        "CONTROL_EVIDENCE",
        "VALIDATION_REPORT",
    }
    runtime_rows = runtime["candidate_artifacts"]
    runtime_types = {row["artifact_type"] for row in runtime_rows}
    if runtime_types != expected_candidate_types:
        return "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET"
    if runtime["candidate_artifact_count"] != len(runtime_rows):
        return "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET"
    path_by_type = {**fixture["paths"]}
    for row in runtime_rows:
        target = row["artifact_type"]
        if target == "HISTORY_SHARD":
            member_raw = fixture["history_shard_members"].get(row["path"])
            if member_raw is None or not _identity_matches(row, member_raw):
                return "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET"
        elif row["path"] != path_by_type[target] or not _identity_matches(
            row, raw[target]
        ):
            return "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET"
    if {
        row["path"]
        for row in runtime_rows
        if row["artifact_type"] == "HISTORY_SHARD"
    } != set(fixture["history_shard_members"]):
        return "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET"
    candidate_root = _artifact_root(
        runtime_rows, b"LOOP_CONTROL_ALL_CANDIDATE_ARTIFACT_ROOT_v2"
    )
    if runtime["candidate_artifact_root_sha256"] != candidate_root:
        return "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET"
    core_types = expected_candidate_types - {
        "CONTROL_EVIDENCE",
        "VALIDATION_REPORT",
    }
    core_rows = [
        row for row in runtime_rows if row["artifact_type"] in core_types
    ]
    core_root = _artifact_root(
        core_rows, b"LOOP_CONTROL_CORE_DATA_ROOT_v2"
    )
    control_rows = control_evidence["control_results"]
    expected_control_ids = [
        profile["control_id"] for profile in _stage_a_profiles()
    ]
    controls_passed = all(row["passed"] for row in control_rows)
    if (
        control_evidence["control_result_count"] != len(control_rows)
        or len(control_rows) != 76
        or [row["control_id"] for row in control_rows]
        != expected_control_ids
        or any(
            row["baseline_core_candidate_root_sha256"] != core_root
            or (row["passed"] and row["observed_error_codes"])
            or (not row["passed"] and not row["observed_error_codes"])
            for row in control_rows
        )
        or control_evidence["baseline_core_candidate_root_sha256"]
        != core_root
        or control_evidence["results_root_sha256"]
        != _stage_a_control_results_root(control_rows)
        or control_evidence["all_results_passed"] != controls_passed
        or control_evidence["status"]
        != ("ALL_76_CONTROLS_PASSED" if controls_passed else "B_BLOCKED")
        or validation_report["candidate_root_sha256"] != core_root
        or validation_report["trust_anchor_sha256"]
        != sha256(raw["REVIEWED_TRUST_ANCHORS"])
        or validation_report["passed"] != controls_passed
        or validation_report["status"]
        != ("PASSED" if controls_passed else "FAILED")
        or (controls_passed and validation_report["issues"])
        or (not controls_passed and not validation_report["issues"])
    ):
        return "V2-E-CONTROL-EVIDENCE-MISMATCH"
    expected_decisions = {
        "CONSUMER-RECONCILIATION": True,
        "CONTROL-OUTCOME": controls_passed,
    }
    observed_decisions = {
        row["decision_id"]: row["passed"]
        for row in report["validator_decisions"]
    }
    if (
        len(observed_decisions) != len(report["validator_decisions"])
        or observed_decisions != expected_decisions
        or report["preflight_consumer_identity_root_sha256"] != all_root
        or report["candidate_consumer_identity_root_sha256"] != all_root
        or report["runtime_required_identity_root_sha256"] != runtime_root
    ):
        return "V2-E-EXECUTION-REPORT-DECISION-MISMATCH"
    if not _identity_matches(runtime["source_manifest"], raw["SOURCE_MANIFEST"]):
        return "V1-E-RUNTIME-SOURCE-MANIFEST-BINDING-MISMATCH"
    if not _identity_matches(report["runtime_manifest"], raw["RUNTIME_MANIFEST"]):
        return "V2-E-EXECUTION-RUNTIME-MANIFEST-BINDING-MISMATCH"
    if not _identity_matches(report["control_evidence"], raw["CONTROL_EVIDENCE"]):
        return "V2-E-EXECUTION-CONTROL-EVIDENCE-BINDING-MISMATCH"
    if not _identity_matches(terminal["source_manifest"], raw["SOURCE_MANIFEST"]):
        return "V2-E-TERMINAL-SOURCE-BINDING-MISMATCH"
    if not _identity_matches(terminal["runtime_manifest"], raw["RUNTIME_MANIFEST"]):
        return "V2-E-TERMINAL-RUNTIME-BINDING-MISMATCH"
    if not _identity_matches(terminal["execution_report"], raw["EXECUTION_REPORT"]):
        return "V2-E-TERMINAL-REPORT-BINDING-MISMATCH"
    if terminal["candidate_artifact_root_sha256"] != candidate_root:
        return "V1-E-TERMINAL-CANDIDATE-COVERAGE"
    if not _identity_matches(review["terminal_envelope"], raw["TERMINAL_ENVELOPE"]):
        return "V1-E-REVIEW-MISSING-TERMINAL-ENVELOPE"
    if not _identity_matches(
        review["review_inventory"], raw["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"]
    ):
        return "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"

    if (
        not review["independent_rescan_performed"]
        or review["inventory_source"] != "INDEPENDENT_GIT_OBJECT_RESCAN"
        or review_inventory["inventory_origin"]
        != "INDEPENDENT_REVIEW_GIT_OBJECT_RESCAN"
    ):
        return "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"
    review_rows = review_inventory["consumers"]
    if review_rows != _independent_review_consumer_rows():
        return "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"
    review_ids = [row["consumer_id"] for row in review_rows]
    review_runtime_ids = [
        row["consumer_id"] for row in review_rows if row["runtime_required"]
    ]
    review_delta_rows = _independent_review_baseline_delta_rows(review_rows)
    review_root = _identity_root(review_ids, review=True)
    review_runtime_root = _runtime_identity_root(review_runtime_ids, review=True)
    if (
        review_inventory.get("source_commit") != SOURCE_COMMIT
        or review_inventory.get("source_tree") != SOURCE_TREE
        or review_inventory.get("algorithm_id")
        != "LOOP_CONTROL_CONSUMER_DISCOVERY_CALLSITE_v2"
        or review_inventory.get("scanner_implementation_id")
        != "INDEPENDENT_REVIEW_FULL_TREE_CAT_FILE_SCANNER_v2"
        or len(review_ids) != len(set(review_ids))
        or any(row["consumer_id"] != _consumer_id(row) for row in review_rows)
        or any(
            row["runtime_required"] != _derived_runtime_required(row)
            for row in review_rows
        )
        or sorted(
            (
                _consumer_reconciliation_projection(row)
                for row in review_rows
            ),
            key=lambda row: row["consumer_id"],
        )
        != sorted(
            (
                _consumer_reconciliation_projection(row)
                for row in preflight_rows
            ),
            key=lambda row: row["consumer_id"],
        )
        or review_inventory["consumer_identity_count"] != len(review_rows)
        or review_inventory["runtime_required_count"] != len(review_runtime_ids)
        or review_inventory["nonruntime_count"]
        != len(review_rows) - len(review_runtime_ids)
        or review_inventory["unique_path_count"]
        != len({row["path"] for row in review_rows})
        or review_inventory["consumer_identity_root_sha256"] != review_root
        or review_inventory["runtime_required_identity_root_sha256"]
        != review_runtime_root
        or sorted(
            review_inventory["baseline_delta_rows"],
            key=lambda row: (row["path"], row["classification"]),
        )
        != review_delta_rows
        or review_inventory["baseline_delta_root_sha256"]
        != _delta_root(review_delta_rows, review=True)
        or review["execution_inventory_root_sha256"] != all_root
        or review["independent_rescan_root_sha256"] != review_root
    ):
        return "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"

    # Enforce every reviewed instance edge against independently derived
    # target bytes or set roots.  Ad-hoc cross-document checks above retain
    # their fault-specific diagnostics; this total map closes any uncovered
    # external or logical target rather than silently trusting a 64-hex leaf.
    expected_target_hashes: dict[str, set[str]] = {}

    def bind_expected(target: str, *hashes: str) -> None:
        expected_target_hashes.setdefault(target, set()).update(hashes)

    for target, target_raw in raw.items():
        if target != "HISTORY_SHARD":
            bind_expected(target, sha256(target_raw))
    bind_expected(
        "HISTORY_SHARD",
        *(sha256(value) for value in expected_history["members"].values()),
    )
    for target in (
        "ACCEPTED_V2_INDEPENDENT_REVIEW",
        "AUTHORIZED_IMPLEMENTATION",
        "EXECUTION_PROTOCOL",
        "SOURCE_REGISTRY",
        "V2_CONTRACT",
        "V2_SCHEMA_BUNDLE",
    ):
        bind_expected(target, expected_external[target]["sha256"])
    bind_expected(
        "AUTHORITY_EVIDENCE", EXPECTED_INPUTS[MAINTENANCE_AUTHORITY_REL][0]
    )
    bind_expected(
        "CUSTODY_CONTRACT", EXPECTED_INPUTS[CUSTODY_CONTRACT_REL][0]
    )
    bind_expected(
        "GUARDRAIL_PACKET", EXPECTED_INPUTS[GUARDRAIL_PACKET_REL][0]
    )
    bind_expected(
        "GUARDRAIL_REVIEW", EXPECTED_INPUTS[GUARDRAIL_REVIEW_REL][0]
    )
    bind_expected("ALLOWED_OUTPUT_PATH_SET", _allowed_output_paths_root())
    bind_expected("PRE_RUN_INVENTORY_SET", _pre_run_inventory_root())
    bind_expected("BASELINE_DELTA_SET", expected_delta_root)
    bind_expected("PREFLIGHT_CONSUMER_IDENTITY_SET", all_root)
    bind_expected("PREFLIGHT_RUNTIME_REQUIRED_IDENTITY_SET", runtime_root)
    bind_expected("ALL_CANDIDATE_ARTIFACT_SET", candidate_root)
    bind_expected("CORE_CANDIDATE_ARTIFACT_SET", core_root)
    bind_expected(
        "CONTROL_PROFILE",
        *{
            alternative["properties"]["profile_control_root_sha256"][
                "const"
            ]
            for alternative in schemas["validation_report"]["oneOf"]
        },
    )
    bind_expected(
        "CONTROL_RESULT_SET", _stage_a_control_results_root(control_rows)
    )
    bind_expected(
        "INDEPENDENT_REVIEW_IDENTITY_SET", review_root
    )
    bind_expected(
        "INDEPENDENT_REVIEW_RUNTIME_REQUIRED_SET", review_runtime_root
    )
    bind_expected(
        "INDEPENDENT_REVIEW_BASELINE_DELTA_SET",
        _delta_root(review_delta_rows, review=True),
    )
    bind_expected("LEGACY_RECONSTRUCTED_BYTES", REGISTRY_SHA256)
    bind_expected("SOURCE_AUTHORITY_COMMITMENT", AUTHORITY_COMMITMENT_SHA256)
    bind_expected(
        "HISTORY_FULL_RECORD_IDENTITY_SET",
        HISTORY_FULL_RECORD_IDENTITY_ROOT_SHA256,
    )
    bind_expected(
        "HISTORY_IDENTITY_PAYLOAD_POINTER_SET",
        HISTORY_IDENTITY_PAYLOAD_POINTER_ROOT_SHA256,
    )
    bind_expected(
        "HISTORY_ORIGINAL_POINTER_SET", HISTORY_ORIGINAL_POINTER_SET_SHA256
    )
    bind_expected(
        "HISTORY_SHARD_RECORD_ID_SET",
        *(row["record_id_root_sha256"] for row in expected_history["descriptors"]),
    )
    bind_expected(
        "SOURCE_REGISTRY_RECORD_PAYLOAD",
        *(row["payload_sha256"] for row in expected_history["records"]),
    )
    operation_result_hashes = {
        sha256(_modeled_operation_result_bytes(row))
        for row in preflight_rows
        if row["runtime_required"]
    }
    bind_expected(
        "CURRENT_PROJECTION_OPERATION_RESULT", *operation_result_hashes
    )
    bind_expected("SOURCE_REGISTRY_OPERATION_RESULT", *operation_result_hashes)

    expected_execution_rows = _consumer_rows()
    expected_review_rows = _independent_review_consumer_rows()
    bind_expected(
        "REPOSITORY_CONSUMER_SOURCE",
        *(
            row["source_sha256"]
            for row in [*expected_execution_rows, *expected_review_rows]
        ),
    )
    bind_expected(
        "REPOSITORY_CONSUMER_STATEMENT",
        *(
            row["statement_or_call_site_sha256"]
            for row in [*expected_execution_rows, *expected_review_rows]
        ),
    )
    bind_expected(
        "REPOSITORY_CONSUMER_SCAN_OBSERVATION",
        *(
            row["scan_observation_sha256"]
            for row in [*expected_execution_rows, *expected_review_rows]
        ),
    )

    current_artifact_rows = current_projection["current_artifacts"]
    current_artifact_paths = {row["path"] for row in current_artifact_rows}
    current_tree = _git_tree_blob_map(SOURCE_COMMIT)
    if current_artifact_paths - set(current_tree):
        return "V2-E-INSTANCE-HASH-GRAPH-MISMATCH"
    current_blobs = _git_blobs(SOURCE_COMMIT, current_artifact_paths)
    for row in current_artifact_rows:
        path = row["path"]
        expected_identity = {
            "git_blob": current_tree[path],
            "path": path,
            "sha256": sha256(current_blobs[path]),
            "size_bytes": len(current_blobs[path]),
            "source_commit": SOURCE_COMMIT,
        }
        if row != expected_identity:
            return "V2-E-INSTANCE-HASH-GRAPH-MISMATCH"
        bind_expected("SOURCE_CURRENT_ARTIFACT", row["sha256"])
    expected_target_hashes.setdefault("SOURCE_CURRENT_ARTIFACT", set())

    reviewed_targets = {
        row["referenced_artifact_type"] for row in REVIEWED_EDGE_TABLE
    }
    if reviewed_targets - set(expected_target_hashes):
        return "V2-E-INSTANCE-HASH-GRAPH-MISMATCH"
    if any(
        observed_sha not in expected_target_hashes[target]
        for _, _, target, observed_sha in observed_instance_hashes
    ):
        return "V2-E-INSTANCE-HASH-GRAPH-MISMATCH"

    expected_ledger = _full_generation_ledger()
    expected_physical_ledger = _physical_generation_ledger()
    if (
        fixture["generation_ledger"] != expected_ledger
        or fixture.get("artifact_generation_ledger")
        != expected_physical_ledger
        or list(raw) != expected_physical_ledger
    ):
        return "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH"
    ordinals = [ARTIFACT_PHASES[node][1] for node in expected_ledger]
    if ordinals != sorted(ordinals) or len(expected_ledger) != len(set(expected_ledger)):
        return "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH"

    complete = branch == "COMPLETE"
    if controls_passed != complete:
        return "V2-E-CONTROL-EVIDENCE-MISMATCH"
    statuses = (
        runtime["status"],
        report["status"],
        terminal["candidate_status"],
        review["decision"],
    )
    expected_statuses = (
        (
            "CANDIDATE_COMPLETE",
            "STAGE_A_CANDIDATE_COMPLETE",
            "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW",
            "ACCEPT_STAGE_A_CANDIDATE_ONLY",
        )
        if complete
        else (
            "B_BLOCKED_CANDIDATE_PRESERVED",
            "B_BLOCKED_CANDIDATE_PRESERVED",
            "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED",
            "B_BLOCKED",
        )
    )
    if statuses != expected_statuses:
        return "V2-E-LIFECYCLE-STATUS-MISMATCH"
    if not (
        runtime["block_reason_codes"]
        == report["block_reason_codes"]
        == terminal["block_reason_codes"]
    ):
        return "V2-E-LIFECYCLE-STATUS-MISMATCH"
    if complete and any(
        (runtime["block_reason_codes"], report["block_reason_codes"], terminal["block_reason_codes"])
    ):
        return "V2-E-LIFECYCLE-STATUS-MISMATCH"
    if not complete and not all(
        (runtime["block_reason_codes"], report["block_reason_codes"], terminal["block_reason_codes"])
    ):
        return "V2-E-LIFECYCLE-STATUS-MISMATCH"
    return None


def simulate_preflight_failure(
    prototype_root: Path, failure: str
) -> tuple[int, dict[str, Any], bytes]:
    mapping = {
        "registry": (
            "blocked_preflight_source_registry_mismatch",
            "V2-E-SOURCE-REGISTRY-MISMATCH",
        ),
        "inventory": (
            "blocked_preflight_consumer_rescan_failure",
            "V2-E-CONSUMER-RESCAN-FAILURE",
        ),
        "graph": (
            "blocked_preflight_hash_graph_invalid",
            "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH",
        ),
        "schema": (
            "blocked_preflight_schema_edge_coverage_failure",
            "V2-E-HASH-FIELD-UNDECLARED",
        ),
    }
    classification, code = mapping[failure]
    diagnostic = {
        "schema_id": "LOOP_CONTROL_STAGE_A_PREFLIGHT_DIAGNOSTIC_v2",
        "classification": classification,
        "error_code": code,
        "message": f"Stage A preflight stopped before prototype creation: {code}",
        "exit_code": 2,
        "candidate_set_created": False,
        "prototype_run_root_created": False,
        "controls_observed": 0,
    }
    Draft202012Validator(build_runtime_schemas()["preflight_diagnostic"]).validate(
        diagnostic
    )
    raw = canonical_json_bytes(diagnostic)
    if prototype_root.exists() or len(raw) > 16_384:
        raise V2PreparationError("preflight diagnostic boundary violated")
    return 2, diagnostic, raw


def _rebind_runtime_and_later(fixture: dict[str, Any]) -> None:
    documents = fixture["documents"]
    raw = fixture["artifact_bytes"]
    runtime = documents["RUNTIME_MANIFEST"]
    for row in runtime["candidate_artifacts"]:
        target = row["artifact_type"]
        target_raw = (
            fixture["history_shard_members"][row["path"]]
            if target == "HISTORY_SHARD"
            else raw[target]
        )
        row.update(_identity(row["path"], target_raw))
    runtime["candidate_artifact_count"] = len(runtime["candidate_artifacts"])
    runtime["candidate_artifact_root_sha256"] = _artifact_root(
        runtime["candidate_artifacts"],
        b"LOOP_CONTROL_ALL_CANDIDATE_ARTIFACT_ROOT_v2",
    )
    _refresh_document_bytes(fixture, "RUNTIME_MANIFEST")
    report = documents["EXECUTION_REPORT"]
    report["runtime_manifest"] = _identity(
        report["runtime_manifest"]["path"], raw["RUNTIME_MANIFEST"]
    )
    report["control_evidence"] = _identity(
        report["control_evidence"]["path"], raw["CONTROL_EVIDENCE"]
    )
    _refresh_document_bytes(fixture, "EXECUTION_REPORT")
    terminal = documents["TERMINAL_ENVELOPE"]
    terminal["runtime_manifest"] = _identity(
        terminal["runtime_manifest"]["path"], raw["RUNTIME_MANIFEST"]
    )
    terminal["execution_report"] = _identity(
        terminal["execution_report"]["path"], raw["EXECUTION_REPORT"]
    )
    terminal["candidate_artifact_root_sha256"] = runtime[
        "candidate_artifact_root_sha256"
    ]
    _refresh_document_bytes(fixture, "TERMINAL_ENVELOPE")
    review = documents["INDEPENDENT_REVIEW"]
    review["terminal_envelope"] = _identity(
        review["terminal_envelope"]["path"], raw["TERMINAL_ENVELOPE"]
    )
    _refresh_document_bytes(fixture, "INDEPENDENT_REVIEW")


def _rebind_core_candidate_chain(fixture: dict[str, Any]) -> None:
    """Rehash every candidate-local consumer-map descendant in phase order."""

    documents = fixture["documents"]
    raw = fixture["artifact_bytes"]
    paths = fixture["paths"]
    history = documents["HISTORY_INDEX"]
    history["consumer_source_map_pointer"]["sha256"] = sha256(
        raw["CONSUMER_MAP"]
    )
    _refresh_document_bytes(fixture, "HISTORY_INDEX")
    projection = documents["CURRENT_PROJECTION"]
    projection["history_index_pointer"]["sha256"] = sha256(raw["HISTORY_INDEX"])
    _refresh_document_bytes(fixture, "CURRENT_PROJECTION")

    core_types = [
        "CUSTODY_PAYLOAD",
        "HISTORY_SHARD",
        "CONSUMER_MAP",
        "CUSTODY_MANIFEST",
        "LEGACY_RECONSTRUCTION",
        "HISTORY_INDEX",
        "CURRENT_PROJECTION",
        "RUNTIME_TRACE",
        "RUNTIME_TRACE_MANIFEST",
        "REVIEWED_TRUST_ANCHORS",
        "ROLLBACK_INVENTORY",
        "WRITER_PROBE",
    ]
    core_rows: list[dict[str, Any]] = []
    for kind in core_types:
        if kind == "HISTORY_SHARD":
            core_rows.extend(
                _candidate_row(kind, path, member_raw)
                for path, member_raw in fixture[
                    "history_shard_members"
                ].items()
            )
        else:
            core_rows.append(_candidate_row(kind, paths[kind], raw[kind]))
    core_root = _artifact_root(core_rows, b"LOOP_CONTROL_CORE_DATA_ROOT_v2")
    validation = documents["VALIDATION_REPORT"]
    validation["candidate_root_sha256"] = core_root
    _refresh_document_bytes(fixture, "VALIDATION_REPORT")
    control = documents["CONTROL_EVIDENCE"]
    control["baseline_core_candidate_root_sha256"] = core_root
    for row in control["control_results"]:
        row["baseline_core_candidate_root_sha256"] = core_root
    control["results_root_sha256"] = _stage_a_control_results_root(
        control["control_results"]
    )
    _refresh_document_bytes(fixture, "CONTROL_EVIDENCE")
    _rebind_runtime_and_later(fixture)


def _rebind_candidate_local_chain(
    fixture: dict[str, Any], *, rebuild_trace: bool
) -> None:
    documents = fixture["documents"]
    raw = fixture["artifact_bytes"]
    candidate_map = documents["CONSUMER_MAP"]
    candidate_ids = [row["consumer_id"] for row in candidate_map["consumers"]]
    runtime_rows = [row for row in candidate_map["consumers"] if row["runtime_required"]]
    runtime_ids = [row["consumer_id"] for row in runtime_rows]
    candidate_map["consumer_identity_count"] = len(candidate_ids)
    candidate_map["runtime_required_count"] = len(runtime_ids)
    candidate_map["nonruntime_count"] = len(candidate_ids) - len(runtime_ids)
    candidate_map["consumer_identity_root_sha256"] = _identity_root(candidate_ids)
    candidate_map["runtime_required_identity_root_sha256"] = _runtime_identity_root(
        runtime_ids
    )
    _refresh_document_bytes(fixture, "CONSUMER_MAP")
    if rebuild_trace:
        allowed = set(runtime_ids)
        fixture["trace_documents"] = [
            event
            for event in fixture["trace_documents"]
            if event["consumer_id"] in allowed
        ]
        raw["RUNTIME_TRACE"] = b"".join(
            compact_json_bytes(event) + b"\n"
            for event in fixture["trace_documents"]
        )
    trace = documents["RUNTIME_TRACE_MANIFEST"]
    trace["consumer_map"] = _identity(
        trace["consumer_map"]["path"], raw["CONSUMER_MAP"]
    )
    trace["runtime_trace"] = _identity(
        trace["runtime_trace"]["path"], raw["RUNTIME_TRACE"]
    )
    if rebuild_trace:
        trace["event_count"] = len(fixture["trace_documents"])
        trace["runtime_required_count"] = len(runtime_ids)
        trace["traced_consumer_identity_root_sha256"] = _runtime_identity_root(
            runtime_ids
        )
        trace["runtime_required_identity_root_sha256"] = _runtime_identity_root(
            runtime_ids
        )
    _refresh_document_bytes(fixture, "RUNTIME_TRACE_MANIFEST")
    documents["EXECUTION_REPORT"][
        "candidate_consumer_identity_root_sha256"
    ] = candidate_map["consumer_identity_root_sha256"]
    if rebuild_trace:
        documents["EXECUTION_REPORT"][
            "runtime_required_identity_root_sha256"
        ] = candidate_map["runtime_required_identity_root_sha256"]
    _rebind_core_candidate_chain(fixture)


def _rebind_after_attestation(fixture: dict[str, Any]) -> None:
    documents = fixture["documents"]
    raw = fixture["artifact_bytes"]
    _refresh_document_bytes(fixture, "EXECUTION_PREFLIGHT_ATTESTATION")
    source = documents["SOURCE_MANIFEST"]
    source["preflight_attestation"] = _identity(
        source["preflight_attestation"]["path"],
        raw["EXECUTION_PREFLIGHT_ATTESTATION"],
    )
    _refresh_document_bytes(fixture, "SOURCE_MANIFEST")
    candidate_map = documents["CONSUMER_MAP"]
    candidate_map["source_manifest"] = _identity(
        candidate_map["source_manifest"]["path"], raw["SOURCE_MANIFEST"]
    )
    _refresh_document_bytes(fixture, "CONSUMER_MAP")
    trace = documents["RUNTIME_TRACE_MANIFEST"]
    trace["source_manifest"] = _identity(
        trace["source_manifest"]["path"], raw["SOURCE_MANIFEST"]
    )
    trace["consumer_map"] = _identity(
        trace["consumer_map"]["path"], raw["CONSUMER_MAP"]
    )
    _refresh_document_bytes(fixture, "RUNTIME_TRACE_MANIFEST")
    documents["RUNTIME_MANIFEST"]["source_manifest"] = _identity(
        documents["RUNTIME_MANIFEST"]["source_manifest"]["path"],
        raw["SOURCE_MANIFEST"],
    )
    documents["TERMINAL_ENVELOPE"]["source_manifest"] = _identity(
        documents["TERMINAL_ENVELOPE"]["source_manifest"]["path"],
        raw["SOURCE_MANIFEST"],
    )
    _rebind_core_candidate_chain(fixture)


V2_NEGATIVE_CONTROLS: Final = [
    (
        "V2-NC-001",
        "declared_graph_differs_from_schema_graph",
        "V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH",
    ),
    (
        "V2-NC-002",
        "schema_graph_differs_from_generation_order",
        "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH",
    ),
    (
        "V2-NC-003",
        "undeclared_hash_bearing_field",
        "V2-E-HASH-FIELD-UNDECLARED",
    ),
    (
        "V2-NC-004",
        "later_phase_artifact_required_too_early",
        "V2-E-LATER-PHASE-REFERENCE",
    ),
    (
        "V2-NC-005",
        "consumer_map_truncated_to_one_row",
        "V2-E-CONSUMER-INVENTORY-INCOMPLETE",
    ),
    (
        "V2-NC-006",
        "trace_truncated_to_match_consumer_map",
        "V2-E-RUNTIME-TRACE-INCOMPLETE",
    ),
    (
        "V2-NC-007",
        "consumer_map_and_trace_locally_rebound",
        "V2-E-CONSUMER-LOCAL-REBIND",
    ),
    (
        "V2-NC-008",
        "stale_historical_count_treated_as_current_truth",
        "V2-E-STALE-CONSUMER-COUNT",
    ),
    (
        "V2-NC-009",
        "fresh_consumer_omitted",
        "V2-E-FRESH-CONSUMER-OMITTED",
    ),
    (
        "V2-NC-010",
        "invented_consumer_inserted",
        "V2-E-CONSUMER-INVENTED",
    ),
    (
        "V2-NC-011",
        "runtime_required_consumer_classified_nonruntime",
        "V2-E-RUNTIME-REQUIRED-MISCLASSIFIED",
    ),
    (
        "V2-NC-012",
        "baseline_path_changed_without_delta_classification",
        "V2-E-BASELINE-CHANGE-UNCLASSIFIED",
    ),
    (
        "V2-NC-013",
        "preflight_inventory_altered_after_source_manifest_creation",
        "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH",
    ),
    (
        "V2-NC-014",
        "consumer_inventory_derived_from_candidate",
        "V2-E-CONSUMER-INVENTORY-TRUST-ROOT",
    ),
    (
        "V2-NC-015",
        "review_trusts_execution_inventory_without_rescan",
        "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED",
    ),
]


SUCCESSOR_NEGATIVE_CONTROLS: Final = [
    *v1.SUCCESSOR_NEGATIVE_CONTROLS,
    *V2_NEGATIVE_CONTROLS,
]


def _rebind_after_inventory(fixture: dict[str, Any]) -> None:
    documents = fixture["documents"]
    raw = fixture["artifact_bytes"]
    _refresh_document_bytes(fixture, "PREFLIGHT_CONSUMER_INVENTORY")
    inventory = documents["PREFLIGHT_CONSUMER_INVENTORY"]
    attestation = documents["EXECUTION_PREFLIGHT_ATTESTATION"]
    attestation["consumer_inventory"] = _identity(
        attestation["consumer_inventory"]["path"],
        raw["PREFLIGHT_CONSUMER_INVENTORY"],
    )
    attestation["baseline_delta_root_sha256"] = inventory[
        "baseline_delta_root_sha256"
    ]
    candidate_map = documents["CONSUMER_MAP"]
    candidate_map["preflight_inventory"] = _identity(
        candidate_map["preflight_inventory"]["path"],
        raw["PREFLIGHT_CONSUMER_INVENTORY"],
    )
    trace = documents["RUNTIME_TRACE_MANIFEST"]
    trace["preflight_inventory"] = _identity(
        trace["preflight_inventory"]["path"],
        raw["PREFLIGHT_CONSUMER_INVENTORY"],
    )
    _rebind_after_attestation(fixture)


def _fixture_root(fixture: dict[str, Any]) -> str:
    return sha256(
        b"LOOP_CONTROL_V2_LIFECYCLE_FIXTURE_ROOT\0"
        + b"\n".join(
            artifact.encode("utf-8")
            + b"\0"
            + fixture["artifact_bytes"][artifact]
            for artifact in fixture["artifact_generation_ledger"]
        )
        + b"\0LOGICAL_GENERATION_LEDGER\0"
        + "\n".join(fixture["generation_ledger"]).encode("utf-8")
    )


def _observe_legacy_control(mutation: str) -> str | None:
    """Mutate a real lifecycle witness and obtain the validator's exact code."""

    fixture = build_lifecycle_fixture("COMPLETE")
    documents = fixture["documents"]
    raw = fixture["artifact_bytes"]
    if mutation == "source_manifest_inventories_runtime_manifest":
        documents["SOURCE_MANIFEST"]["runtime_manifest"] = _identity(
            "manifests/runtime_manifest.json", raw["RUNTIME_MANIFEST"]
        )
    elif mutation == "runtime_manifest_omits_source_manifest_binding":
        documents["RUNTIME_MANIFEST"].pop("source_manifest")
    elif mutation == "runtime_manifest_binds_modified_source_manifest":
        documents["RUNTIME_MANIFEST"]["source_manifest"]["sha256"] = "0" * 64
        _refresh_document_bytes(fixture, "RUNTIME_MANIFEST")
    elif mutation == "terminal_envelope_included_in_earlier_manifest":
        documents["RUNTIME_MANIFEST"]["terminal_envelope"] = _identity(
            "manifests/terminal_envelope.json", raw["TERMINAL_ENVELOPE"]
        )
    elif mutation == "terminal_envelope_hashes_itself":
        documents["TERMINAL_ENVELOPE"]["self_sha256"] = sha256(
            raw["TERMINAL_ENVELOPE"]
        )
    elif mutation == "execution_report_and_terminal_bind_reciprocally":
        documents["EXECUTION_REPORT"]["terminal_envelope"] = _identity(
            "manifests/terminal_envelope.json", raw["TERMINAL_ENVELOPE"]
        )
    elif mutation == "candidate_rebinds_external_expected_source_hash":
        documents["SOURCE_MANIFEST"]["source_registry"]["sha256"] = "0" * 64
        _refresh_document_bytes(fixture, "SOURCE_MANIFEST")
    elif mutation == "runtime_manifest_precedes_candidate_finalization":
        ledger = fixture["generation_ledger"]
        ledger.remove("RUNTIME_MANIFEST")
        ledger.insert(ledger.index("VALIDATION_REPORT"), "RUNTIME_MANIFEST")
    elif mutation == "source_manifest_contains_temporary_or_wall_clock_field":
        documents["SOURCE_MANIFEST"]["temporary_path"] = "C:/temporary"
    elif mutation == "review_accepts_chain_without_terminal_envelope":
        documents["INDEPENDENT_REVIEW"].pop("terminal_envelope")
    elif mutation == "terminal_envelope_omits_candidate_shard":
        retained = [
            row
            for row in documents["RUNTIME_MANIFEST"]["candidate_artifacts"]
            if row["artifact_type"] != "HISTORY_SHARD"
        ]
        documents["TERMINAL_ENVELOPE"]["candidate_artifact_root_sha256"] = (
            _artifact_root(
                retained, b"LOOP_CONTROL_ALL_CANDIDATE_ARTIFACT_ROOT_v2"
            )
        )
        _refresh_document_bytes(fixture, "TERMINAL_ENVELOPE")
        documents["INDEPENDENT_REVIEW"]["terminal_envelope"] = _identity(
            documents["INDEPENDENT_REVIEW"]["terminal_envelope"]["path"],
            raw["TERMINAL_ENVELOPE"],
        )
        _refresh_document_bytes(fixture, "INDEPENDENT_REVIEW")
    elif mutation == "terminal_envelope_binds_execution_report_from_other_run":
        documents["TERMINAL_ENVELOPE"]["run_id"] = "other_run"
    else:
        raise V2PreparationError(f"unknown legacy mutation: {mutation}")
    return validate_lifecycle_fixture(fixture)


def _observe_v2_control(mutation: str) -> str | None:
    if mutation == "declared_graph_differs_from_schema_graph":
        schemas = build_runtime_schemas()
        edges = derive_reviewed_edge_table(schemas)
        declared = deepcopy(edges)
        declared.pop()
        try:
            validate_schema_derived_graph(
                schemas, edges, declared_edge_table=declared
            )
        except V2PreparationError as error:
            return str(error)
        return None
    if mutation == "undeclared_hash_bearing_field":
        schemas = build_runtime_schemas()
        source = schemas["execution_source_manifest"]
        source["properties"]["rogue_optional_sha256"] = {
            "pattern": "^[0-9a-f]{64}$",
            "type": "string",
        }
        try:
            derive_reviewed_edge_table(schemas)
        except V2PreparationError as error:
            return str(error).split(":", 1)[0]
        return None
    if mutation == "later_phase_artifact_required_too_early":
        schemas = build_runtime_schemas()
        source = schemas["execution_source_manifest"]
        source["properties"]["terminal_envelope_sha256"] = _sha_schema(
            "TERMINAL_ENVELOPE"
        )
        source["required"].append("terminal_envelope_sha256")
        edges = derive_reviewed_edge_table(schemas)
        try:
            validate_schema_derived_graph(schemas, edges)
        except V2PreparationError as error:
            return str(error)
        return None

    fixture = build_lifecycle_fixture("COMPLETE")
    documents = fixture["documents"]
    if mutation == "schema_graph_differs_from_generation_order":
        ledger = fixture["generation_ledger"]
        consumer_index = ledger.index("CONSUMER_MAP")
        custody_index = ledger.index("CUSTODY_PAYLOAD")
        ledger[consumer_index], ledger[custody_index] = (
            ledger[custody_index],
            ledger[consumer_index],
        )
    elif mutation == "consumer_map_truncated_to_one_row":
        documents["CONSUMER_MAP"]["consumers"] = documents["CONSUMER_MAP"][
            "consumers"
        ][:1]
        _rebind_candidate_local_chain(fixture, rebuild_trace=False)
    elif mutation == "trace_truncated_to_match_consumer_map":
        fixture["trace_documents"] = fixture["trace_documents"][:1]
        fixture["artifact_bytes"]["RUNTIME_TRACE"] = b"".join(
            compact_json_bytes(event) + b"\n"
            for event in fixture["trace_documents"]
        )
        trace = documents["RUNTIME_TRACE_MANIFEST"]
        trace["runtime_trace"] = _identity(
            trace["runtime_trace"]["path"], fixture["artifact_bytes"]["RUNTIME_TRACE"]
        )
        trace["event_count"] = 1
        _refresh_document_bytes(fixture, "RUNTIME_TRACE_MANIFEST")
        _rebind_core_candidate_chain(fixture)
    elif mutation == "consumer_map_and_trace_locally_rebound":
        documents["CONSUMER_MAP"]["consumers"] = [
            next(
                row
                for row in documents["CONSUMER_MAP"]["consumers"]
                if row["runtime_required"]
            )
        ]
        _rebind_candidate_local_chain(fixture, rebuild_trace=True)
    elif mutation == "stale_historical_count_treated_as_current_truth":
        documents["EXECUTION_PREFLIGHT_ATTESTATION"]["consumer_identity_count"] = 520
        documents["SOURCE_MANIFEST"]["consumer_identity_count"] = 520
        _rebind_after_attestation(fixture)
    elif mutation == "fresh_consumer_omitted":
        documents["CONSUMER_MAP"]["consumers"].pop()
        _rebind_candidate_local_chain(fixture, rebuild_trace=False)
    elif mutation == "invented_consumer_inserted":
        invented = deepcopy(documents["CONSUMER_MAP"]["consumers"][0])
        invented["path"] = "formal/python/tools/invented_consumer.py"
        invented["source_sha256"] = "f" * 64
        invented["statement_or_call_site_sha256"] = "a" * 64
        invented["git_blob"] = "f" * 40
        invented["consumer_id"] = _consumer_id(invented)
        documents["CONSUMER_MAP"]["consumers"].append(invented)
        _rebind_candidate_local_chain(fixture, rebuild_trace=False)
    elif mutation == "runtime_required_consumer_classified_nonruntime":
        row = next(
            row
            for row in documents["CONSUMER_MAP"]["consumers"]
            if row["runtime_required"]
        )
        row["runtime_required"] = False
        _rebind_candidate_local_chain(fixture, rebuild_trace=False)
    elif mutation == "baseline_path_changed_without_delta_classification":
        inventory = documents["PREFLIGHT_CONSUMER_INVENTORY"]
        inventory["baseline_delta_rows"] = [
            row for row in inventory["baseline_delta_rows"] if row["path"] != "README.md"
        ]
        inventory["baseline_delta_root_sha256"] = _delta_root(
            inventory["baseline_delta_rows"]
        )
        _rebind_after_inventory(fixture)
    elif mutation == "preflight_inventory_altered_after_source_manifest_creation":
        documents["PREFLIGHT_CONSUMER_INVENTORY"]["source_tree"] = "0" * 40
        _refresh_document_bytes(fixture, "PREFLIGHT_CONSUMER_INVENTORY")
    elif mutation == "consumer_inventory_derived_from_candidate":
        documents["EXECUTION_PREFLIGHT_ATTESTATION"][
            "candidate_supplied_inventory_used"
        ] = True
        _rebind_after_attestation(fixture)
    elif mutation == "review_trusts_execution_inventory_without_rescan":
        copied = deepcopy(documents["PREFLIGHT_CONSUMER_INVENTORY"])
        copied["schema_id"] = (
            "LOOP_CONTROL_INDEPENDENT_REVIEW_CONSUMER_INVENTORY_v2"
        )
        copied["inventory_origin"] = "INDEPENDENT_REVIEW_GIT_OBJECT_RESCAN"
        documents["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"] = copied
        _refresh_document_bytes(
            fixture, "INDEPENDENT_REVIEW_CONSUMER_INVENTORY"
        )
        review_document = documents["INDEPENDENT_REVIEW"]
        review_document["review_inventory"] = _identity(
            review_document["review_inventory"]["path"],
            fixture["artifact_bytes"][
                "INDEPENDENT_REVIEW_CONSUMER_INVENTORY"
            ],
        )
        _refresh_document_bytes(fixture, "INDEPENDENT_REVIEW")
    else:
        raise V2PreparationError(f"unknown v2 mutation: {mutation}")
    return validate_lifecycle_fixture(fixture)


def run_permanent_negative_controls() -> list[dict[str, Any]]:
    for branch in ("COMPLETE", "POST_GENERATION_BLOCKED"):
        baseline = build_lifecycle_fixture(branch)
        if validate_lifecycle_fixture(baseline) is not None:
            raise V2PreparationError(f"positive {branch} lifecycle does not validate")
    baseline_root = _fixture_root(build_lifecycle_fixture("COMPLETE"))
    results: list[dict[str, Any]] = []
    for control_id, mutation, expected in SUCCESSOR_NEGATIVE_CONTROLS:
        observed = (
            _observe_legacy_control(mutation)
            if control_id.startswith("DAG-V1-")
            else _observe_v2_control(mutation)
        )
        results.append(
            {
                "baseline_recreated": True,
                "baseline_root_sha256_after": baseline_root,
                "baseline_root_sha256_before": baseline_root,
                "control_id": control_id,
                "expected_error_code": expected,
                "local_candidate_hashes_rebound": mutation
                in {
                    "consumer_map_truncated_to_one_row",
                    "trace_truncated_to_match_consumer_map",
                    "consumer_map_and_trace_locally_rebound",
                },
                "mutation": mutation,
                "observed_error_code": observed,
                "passed": observed == expected,
                "subsequent_controls_unmodified": True,
            }
        )
    failures = [row for row in results if not row["passed"]]
    if failures:
        raise V2PreparationError(
            "permanent control mismatch: "
            + ", ".join(
                f"{row['control_id']}={row['observed_error_code']}"
                for row in failures
            )
        )
    return results


def run_negative_controls() -> list[dict[str, Any]]:
    """Compatibility name for the exact 27 permanent controls."""

    return [
        {
            **row,
            "baseline_sha256_after": row["baseline_root_sha256_after"],
            "baseline_sha256_before": row["baseline_root_sha256_before"],
        }
        for row in run_permanent_negative_controls()
    ]


_TYPED_SCAN_CACHE: dict[str, dict[str, Any]] = {}


def _typed_legacy_classification(
    path: str, runtime_required: bool
) -> tuple[str, str, str]:
    suffix = Path(path).suffix.lower()
    if path in NONLITERAL_READERS:
        category = "INDIRECT_API_CONSUMER"
        mechanism = "REVIEWED_NONLITERAL_PATH_RULE"
    elif "/tests/" in f"/{path}":
        category = "TEST_ONLY"
        mechanism = "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    elif suffix in {".md", ".txt", ".lean"}:
        category = "DOCUMENTATION_ONLY"
        mechanism = "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    elif path.startswith(("archive/", "backup/")):
        category = "HISTORICAL_ONLY"
        mechanism = "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    elif path.startswith("formal/docs/release/") and suffix == ".json":
        category = "GENERATED_REFERENCE"
        mechanism = "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    elif "integrity" in path and runtime_required:
        category = "WRITER"
        mechanism = "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    elif runtime_required:
        category = "DIRECT_READER"
        mechanism = "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    else:
        category = "GENERATED_REFERENCE"
        mechanism = "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    if not runtime_required:
        operation = "LITERAL_REFERENCE_ONLY"
    elif category == "WRITER":
        operation = "MUTATE_REGISTRY"
    elif "schema" in path.lower() or "validat" in path.lower():
        operation = "VALIDATE_ROOT_SCHEMA"
    elif "hash" in path.lower() or "integrity" in path.lower():
        operation = "COMPARE_HASH"
    else:
        operation = "READ_CURRENT_AUTHORITY"
    return category, operation, mechanism


def scan_legacy_consumer_surface(commit: str) -> dict[str, Any]:
    """Type the legacy path scan as evidence, never as an execution count oracle."""

    cached = _TYPED_SCAN_CACHE.get(commit)
    if cached is not None:
        return deepcopy(cached)
    baseline = _strict_json(_git_blob(SOURCE_COMMIT, BASELINE_CONSUMER_REL))
    baseline_by_path = {row["path"]: row for row in baseline["consumers"]}
    baseline_paths = set(baseline_by_path)
    current_paths = _git_literal_consumer_paths(commit) | set(NONLITERAL_READERS)
    tree = _git_tree_blob_map(commit)
    changed = {
        path
        for path in current_paths & baseline_paths
        if tree[path] != baseline_by_path[path]["git_blob"]
    }
    grep = subprocess.run(
        ["git", "grep", "-n", "-F", "LOOP_CONTROL_REGISTRY_v0.json", commit, "--"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    matched_statements: dict[str, list[str]] = {}
    prefix = commit + ":"
    for line in grep.stdout.splitlines():
        value = line[len(prefix) :] if line.startswith(prefix) else line
        parts = value.split(":", 2)
        if len(parts) == 3 and parts[0] != REGISTRY_REL:
            matched_statements.setdefault(parts[0], []).append(
                f"{parts[1]}:{parts[2].strip()}"
            )
    for path in NONLITERAL_READERS:
        matched_statements.setdefault(path, ["REVIEWED_NONLITERAL_READER_v2"])
    rows: list[dict[str, Any]] = []
    for path in sorted(current_paths):
        if path in baseline_by_path and path not in changed:
            runtime_required = bool(
                baseline_by_path[path]["runtime_trace_required"]
            )
        else:
            runtime_required = _legacy_runtime_required(
                path, _git_blob(commit, path)
            )
        category, operation, mechanism = _typed_legacy_classification(
            path, runtime_required
        )
        statement_hash = sha256(
            "\n".join(sorted(matched_statements[path])).encode("utf-8")
        )
        identity_row = {
            "consumer_category": category,
            "discovery_mechanism": mechanism,
            "operation_class": operation,
            "path": path,
            "statement_or_call_site_sha256": statement_hash,
        }
        row = {
            **identity_row,
            "runtime_required": runtime_required,
            # Compatibility spelling for callers that distinguish the legacy
            # evidence scan from the normative v2 schema spelling.
            "statement_or_callsite_sha256": statement_hash,
        }
        row["consumer_id"] = _consumer_id(identity_row)
        rows.append(row)
    runtime_count = sum(row["runtime_required"] for row in rows)
    result = {
        "consumer_count": len(rows),
        "consumers": rows,
        "git_commit": commit,
        "non_runtime_count": len(rows) - runtime_count,
        "runtime_required_count": runtime_count,
    }
    _TYPED_SCAN_CACHE[commit] = deepcopy(result)
    return result


def _successor_control_root(rows: list[dict[str, Any]]) -> str:
    return sha256(
        b"LOOP_CONTROL_STAGE_A_V2_SUCCESSOR_REGRESSION_ROOT\0"
        + b"\n".join(compact_json_bytes(row) for row in rows)
    )


_CONTRACT_CACHE: dict[str, Any] | None = None


def _draft_build_contract_facade() -> dict[str, Any]:
    global _CONTRACT_CACHE
    if _CONTRACT_CACHE is not None:
        return deepcopy(_CONTRACT_CACHE)
    bindings = _frozen_input_bindings()
    schemas = build_runtime_schemas()
    model_external_identities = _lifecycle_model_external_identities(schemas)
    edges = derive_schema_edges(schemas)
    topological_order = validate_schema_graph(schemas, edges)
    complete = build_lifecycle_fixture("COMPLETE")
    blocked = build_lifecycle_fixture("POST_GENERATION_BLOCKED")
    if validate_lifecycle_fixture(complete) is not None:
        raise V2PreparationError("complete lifecycle fixture does not validate")
    if validate_lifecycle_fixture(blocked) is not None:
        raise V2PreparationError("blocked lifecycle fixture does not validate")
    preflight_failures = {
        failure: simulate_preflight_failure(REPO_ROOT / PROTOTYPE_ROOT_REL, failure)[1]
        for failure in ("registry", "inventory", "graph", "schema")
    }
    controls = run_permanent_negative_controls()
    current_observation = legacy_path_scan_evidence(SOURCE_COMMIT)
    v1_contract = _strict_json(_git_blob(SOURCE_COMMIT, V1_CONTRACT_REL))
    profiles = v1_contract["stage_a_control_contract"]["exact_control_profiles"]
    phase_table = [
        {
            "artifact_type": artifact,
            "artifact_kind": kind,
            "generation_ordinal": ordinal,
            "generation_phase": phase,
        }
        for artifact, (phase, ordinal, kind) in sorted(
            ARTIFACT_PHASES.items(), key=lambda item: (item[1][1], item[0])
        )
    ]
    contract = {
        "authorization": {
            "consumer_migration_authorized": False,
            "current_authority_cutover_authorized": False,
            "implementation_change_authorized_before_independent_review": False,
            "maintenance_target_rotation_authorized": False,
            "monolith_modification_or_retirement_authorized": False,
            "new_api_writes_authorized": False,
            "prototype_execution_authorized": False,
            "scientific_target_rotation_authorized": False,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumer_inventory_contract": {
            "candidate_identity_set_must_equal_fresh_preflight_identity_set": True,
            "candidate_local_expected_count_allowed": False,
            "candidate_runtime_required_set_must_equal_fresh_preflight_runtime_required_set": True,
            "discovery_and_classification_algorithm": consumer_inventory_algorithm_contract(),
            "execution_inventory_generated_before_candidate_root": True,
            "preparation_commit_legacy_scan_observation": {
                key: current_observation[key]
                for key in (
                    "added_path_count",
                    "changed_baseline_path_count",
                    "nonruntime_path_count",
                    "path_count",
                    "removed_path_count",
                    "runtime_required_path_count",
                    "scan_commit",
                    "sorted_path_lf_root_sha256",
                )
            },
            "preparation_observation_is_future_execution_expectation": False,
            "required_reconciliation_rules": [
                "NO_OMITTED_FRESH_CONSUMERS",
                "NO_INVENTED_CONSUMERS",
                "NO_DUPLICATE_CONSUMER_IDS",
                "NO_UNMATCHED_RUNTIME_TRACES",
                "NO_RUNTIME_REQUIRED_CONSUMER_WITHOUT_TRACE_COVERAGE",
                "NO_CHANGED_BASELINE_PATH_HIDDEN_AS_UNCHANGED",
                "NO_CANDIDATE_LOCAL_EXPECTED_COUNT",
            ],
            "review_must_rescan_same_commit": True,
            "review_must_use_independent_scanner_implementation": True,
            "reviewed_v1_historical_evidence": {
                "added_consumer_count": 24,
                "changed_baseline_path_count": 3,
                "evidence_commit": SOURCE_COMMIT,
                "historical_baseline_consumer_count": 496,
                "is_future_execution_expectation": False,
                "non_runtime_count": 35,
                "removed_consumer_count": 0,
                "reviewed_commit_consumer_count": 520,
                "runtime_required_count": 485,
            },
            "reviewed_v1_scan_subject_commit": (
                "6ce5f8389a8b4ac0cba2ab68ba9f4bb1e39743df"
            ),
        },
        "external_trust_contract": {
            "candidate_may_redefine_expected_hashes": False,
            "frozen_preparation_inputs": bindings,
            "fresh_execution_inventory_is_external_to_candidate_evidence": True,
            "independent_review_hash_known_only_after_review": True,
            "source_manifest_must_bind_preflight_attestation": True,
        },
        "failure_semantics": {
            "candidate_or_control_failure": (
                "PRESERVE_B_BLOCKED_CANDIDATE_RUNTIME_REPORT_AND_TERMINAL_CHAIN_"
                "NO_REVIEW_ACCEPTANCE_NO_STAGE_B"
            ),
            "preflight_failure": (
                "NONZERO_EXIT_BOUNDED_DIAGNOSTIC_ONLY_NO_PROTOTYPE_ROOT_"
                "NO_CANDIDATE_ARTIFACT"
            ),
            "preflight_failure_fixtures": preflight_failures,
            "source_registry_may_change_on_failure": False,
        },
        "generation_phase_table": phase_table,
        "generation_sequence": [
            "REVIEWED_V2_CONTRACT",
            "FRESH_REPOSITORY_SCAN",
            "EXECUTION_PREFLIGHT_ATTESTATION",
            "SOURCE_MANIFEST",
            "PROTOTYPE_CANDIDATES",
            "RUNTIME_MANIFEST",
            "EXECUTION_REPORT",
            "TERMINAL_ENVELOPE",
            "INDEPENDENT_REVIEW_RESCAN_AND_DECISION",
        ],
        "hash_graph_contract": {
            "actual_generation_order": _reviewed_generation_order(),
            "derived_edge_count": len(edges),
            "edge_table": edges,
            "edge_table_root_sha256": sha256(compact_json_bytes(edges)),
            "graph_authority": (
                "MECHANICALLY_DERIVED_FROM_ACTUAL_HASH_BEARING_SCHEMA_FIELDS"
            ),
            "required_validator_rules": [
                "EVERY_SCHEMA_HASH_FIELD_APPEARS_IN_REVIEWED_EDGE_TABLE",
                "REFERENCED_ARTIFACT_EXISTS_BEFORE_CONTAINING_ARTIFACT_GENERATION",
                "TOPOLOGICAL_SORT_SUCCEEDS",
                "EVERY_REQUIRED_NODE_APPEARS_EXACTLY_ONCE",
                "NO_SELF_EDGE",
                "NO_RECIPROCAL_EDGE",
                "NO_EARLIER_PHASE_REFERENCES_LATER_PHASE",
                "COMPLETE_AND_BLOCKED_BRANCHES_EACH_FORM_VALID_SUBGRAPH",
            ],
            "topological_order": topological_order,
        },
        "lifecycle_contract": {
            "complete_branch_fixture_root_sha256": _fixture_root(complete),
            "complete_branch_schema_and_cross_document_valid": True,
            "post_generation_blocked_branch_fixture_root_sha256": _fixture_root(blocked),
            "post_generation_blocked_branch_schema_and_cross_document_valid": True,
            "preflight_blocked_branch_diagnostic_only_valid": True,
            "preflight_blocked_branch_prototype_root_created": False,
            "real_canonical_document_bytes_used": True,
        },
        "nonpromotion": {
            "candidate_artifacts_created": False,
            "current_projection_authoritative": False,
            "maintenance_target": MAINTENANCE_TARGET,
            "monolith_remains_authoritative_and_unchanged": True,
            "prototype_execution_attempted": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
        },
        "runtime_schemas": schemas,
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
            "CONTRACT_BUNDLE_20260712_v2"
        ),
        "source_commit": SOURCE_COMMIT,
        "source_commit_layout": {
            "authorized_implementation_paths_unchanged": {
                path: bindings[path] for path in AUTHORIZED_IMPLEMENTATION_PATHS
            },
            "production_and_prototype_paths_absent": {
                path: not _git_path_exists(SOURCE_COMMIT, path)
                for path in PRODUCTION_LAYOUT_PATHS
            },
        },
        "stage_a_control_contract": {
            "exact_control_ids": [row["control_id"] for row in profiles],
            "exact_control_profile_count": len(profiles),
            "exact_control_profiles": profiles,
            "legacy_cycle_regression_count": len(v1.SUCCESSOR_NEGATIVE_CONTROLS),
            "new_graph_and_inventory_regression_count": len(V2_NEGATIVE_CONTROLS),
            "preterminal_stage_a_control_count": 76,
            "successor_regression_control_count": len(controls),
            "successor_regression_results": controls,
            "successor_regression_results_root_sha256": _successor_control_root(
                controls
            ),
            "successor_regressions_run_against_canonical_cross_document_fixtures": True,
            "successor_regressions_stored_outside_terminal_envelope": True,
        },
        "status": (
            "SCHEMA_DERIVED_GRAPH_AND_EXTERNAL_CONSUMER_ATTESTATION_V2_"
            "PREPARED_INDEPENDENT_REVIEW_REQUIRED_NO_STAGE_A_OR_STAGE_B"
        ),
        "supersession": {
            "effective_only_after_independent_review": True,
            "preserves_v0_and_v1_preparation_implementation_and_review_evidence": True,
            "reason": (
                "DECLARED_GRAPH_MUST_EQUAL_EXECUTABLE_SCHEMA_GRAPH_AND_"
                "CANDIDATE_LOCAL_CONSISTENCY_MUST_RECONCILE_TO_FRESH_REPOSITORY_INVENTORY"
            ),
            "v1_blocked_review": bindings[V1_REVIEW_REL],
        },
    }
    _CONTRACT_CACHE = deepcopy(contract)
    return contract


def _draft_build_packet_facade() -> dict[str, Any]:
    contract_raw = canonical_json_bytes(_draft_build_contract_facade())
    return {
        "authorization": {
            "implementation_change_authorized": False,
            "independent_review_required": True,
            "maintenance_target_rotation_authorized": False,
            "prototype_execution_authorized": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_target_rotation_authorized": False,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "boundary": {
            "candidate_artifacts_created": False,
            "consumer_migration_started": False,
            "legacy_monolith_modified_or_retired": False,
            "prototype_execution_attempted": False,
            "scientific_artifacts_or_claims_changed": False,
            "v1_preparation_or_blocked_review_amended": False,
            "v2_contract_prepared_only": True,
        },
        "captured_at_utc": CAPTURED_AT_UTC,
        "contract_bundle": {"path": CONTRACT_REL, "sha256": sha256(contract_raw)},
        "counts": {
            "existing_stage_a_control_count": 76,
            "legacy_cycle_regression_count": len(v1.SUCCESSOR_NEGATIVE_CONTROLS),
            "new_graph_and_inventory_regression_count": len(V2_NEGATIVE_CONTROLS),
            "runtime_schema_count": RUNTIME_SCHEMA_COUNT,
            "schema_hash_edge_count": len(REVIEWED_EDGE_TABLE),
        },
        "execution_target_recommended_not_selected": EXECUTION_TARGET,
        "maintenance_target": MAINTENANCE_TARGET,
        "packet_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
            "PACKET_20260712_v2"
        ),
        "packet_target": PACKET_TARGET,
        "review_target_recommended_not_selected": REVIEW_TARGET,
        "scientific_target": SCIENTIFIC_TARGET,
        "source_commit": SOURCE_COMMIT,
        "status": (
            "V2_EXECUTION_CONTRACT_PREPARED_INDEPENDENT_REVIEW_REQUIRED_"
            "NO_STAGE_A_STAGE_B_MIGRATION_CUTOVER_OR_SCIENCE"
        ),
    }


def _draft_build_all_facade() -> dict[Path, bytes]:
    return {
        CONTRACT_PATH: canonical_json_bytes(_draft_build_contract_facade()),
        PACKET_PATH: canonical_json_bytes(_draft_build_packet_facade()),
    }


def _draft_atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
        delete=False,
    ) as handle:
        temporary = Path(handle.name)
        handle.write(raw)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def _draft_main_facade() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = _draft_build_all_facade()
    if args.write:
        for path, raw in outputs.items():
            _draft_atomic_write(path, raw)
        return 0
    mismatches = [
        path.relative_to(REPO_ROOT).as_posix()
        for path, raw in outputs.items()
        if not path.exists() or path.read_bytes() != raw
    ]
    if mismatches:
        raise V2PreparationError(
            "V2-E-GENERATED-ARTIFACT-DRIFT:" + ",".join(mismatches)
        )
    return 0


def _edge_table_root(rows: list[dict[str, Any]]) -> str:
    return sha256(
        b"LOOP_CONTROL_V2_REVIEWED_SCHEMA_HASH_EDGE_TABLE\0"
        + b"\n".join(compact_json_bytes(row) for row in rows)
    )


def _permanent_control_results_root(rows: list[dict[str, Any]]) -> str:
    return sha256(
        b"LOOP_CONTROL_V2_PERMANENT_SUCCESSOR_CONTROL_RESULTS\0"
        + b"\n".join(compact_json_bytes(row) for row in rows)
    )


def _phase_table() -> list[dict[str, Any]]:
    rows = [
        {
            "artifact_type": artifact,
            "blocked_path_applicability": (
                "REQUIRED"
                if "POST_GENERATION_BLOCKED"
                in ARTIFACT_BRANCHES.get(artifact, ())
                else "LOGICAL_OR_EXTERNAL"
            ),
            "complete_path_applicability": (
                "REQUIRED"
                if "COMPLETE" in ARTIFACT_BRANCHES.get(artifact, ())
                else "LOGICAL_OR_EXTERNAL"
            ),
            "generation_ordinal": ordinal,
            "generation_phase": phase,
            "node_kind": kind,
        }
        for artifact, (phase, ordinal, kind) in ARTIFACT_PHASES.items()
    ]
    rows.append(
        {
            "artifact_type": "PREFLIGHT_DIAGNOSTIC",
            "blocked_path_applicability": "INAPPLICABLE",
            "complete_path_applicability": "INAPPLICABLE",
            "generation_ordinal": 0,
            "generation_phase": "PREFLIGHT_BLOCKED_ONLY_IN_MEMORY_OR_STDOUT",
            "node_kind": "BOUNDED_DIAGNOSTIC_NOT_PROTOTYPE_ARTIFACT",
        }
    )
    return sorted(rows, key=lambda row: (row["generation_ordinal"], row["artifact_type"]))


def _build_contract_uncached() -> dict[str, Any]:
    bindings = _frozen_input_bindings()
    schemas = build_runtime_schemas()
    model_external_identities = _lifecycle_model_external_identities(schemas)
    edge_table = derive_reviewed_edge_table(schemas)
    topological_order = validate_schema_derived_graph(schemas, edge_table)
    controls = run_permanent_negative_controls()
    complete = build_lifecycle_fixture("COMPLETE")
    blocked = build_lifecycle_fixture("POST_GENERATION_BLOCKED")
    if validate_lifecycle_fixture(complete) is not None:
        raise V2PreparationError("complete lifecycle validation failed")
    if validate_lifecycle_fixture(blocked) is not None:
        raise V2PreparationError("blocked lifecycle validation failed")
    reviewed_scan = legacy_path_scan_evidence(
        "6ce5f8389a8b4ac0cba2ab68ba9f4bb1e39743df"
    )
    source_scan = legacy_path_scan_evidence(SOURCE_COMMIT)
    expected_reviewed = (520, 485, 35, 24, 0, 3)
    observed_reviewed = (
        reviewed_scan["path_count"],
        reviewed_scan["runtime_required_path_count"],
        reviewed_scan["nonruntime_path_count"],
        reviewed_scan["added_path_count"],
        reviewed_scan["removed_path_count"],
        reviewed_scan["changed_baseline_path_count"],
    )
    expected_source = (522, 486, 36, 26, 0, 3)
    observed_source = (
        source_scan["path_count"],
        source_scan["runtime_required_path_count"],
        source_scan["nonruntime_path_count"],
        source_scan["added_path_count"],
        source_scan["removed_path_count"],
        source_scan["changed_baseline_path_count"],
    )
    if observed_reviewed != expected_reviewed or observed_source != expected_source:
        raise V2PreparationError("historical path-scan evidence drift")
    stage_a_profiles = _stage_a_profiles()
    stage_a_ids = [row["control_id"] for row in stage_a_profiles]
    return {
        "authorization": {
            "consumer_migration_authorized": False,
            "current_authority_cutover_authorized": False,
            "implementation_change_authorized_before_independent_review": False,
            "maintenance_target_rotation_authorized": False,
            "monolith_modification_or_retirement_authorized": False,
            "new_api_writes_authorized": False,
            "packet_independent_review_required": True,
            "prototype_execution_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_target_rotation_authorized": False,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "captured_at_utc": CAPTURED_AT_UTC,
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
            "CONTRACT_BUNDLE_20260712_v2"
        ),
        "source_commit": SOURCE_COMMIT,
        "external_roots_of_trust": {
            "frozen_preparation_inputs": bindings,
            "predecessor_v1_packet_sha256": V1_PACKET_SHA256,
            "predecessor_v1_contract_sha256": V1_CONTRACT_SHA256,
            "predecessor_v1_blocked_review_sha256": V1_REVIEW_SHA256,
            "source_registry_sha256": REGISTRY_SHA256,
            "reviewed_embedded_v2_schema_catalog_root_sha256": sha256(
                compact_json_bytes(schemas)
            ),
            "reviewed_embedded_v2_schema_catalog_serializer": (
                "COMPACT_CANONICAL_FINITE_JSON_UTF8"
            ),
            "execution_protocol_sha256": model_external_identities[
                "EXECUTION_PROTOCOL"
            ]["sha256"],
            "authorized_implementation_inventory_sha256": (
                model_external_identities["AUTHORIZED_IMPLEMENTATION"][
                    "sha256"
                ]
            ),
            "lifecycle_model_symbolic_future_roots": {
                "accepted_v2_contract_sha256": (
                    MODEL_ACCEPTED_V2_CONTRACT_SHA256
                ),
                "accepted_v2_independent_review_sha256": (
                    MODEL_ACCEPTED_V2_REVIEW_SHA256
                ),
                "model_only_not_future_execution_expectations": True,
            },
            "production_future_root_resolution": (
                "EXECUTION_LOADS_INDEPENDENTLY_ACCEPTED_V2_CONTRACT_AND_REVIEW_"
                "IDENTITIES_OUTSIDE_CANDIDATE_EVIDENCE"
            ),
            "candidate_may_supply_or_rebind_expected_values": False,
            "execution_reads_exact_git_commit_objects": True,
            "review_reloads_exact_execution_commit_objects": True,
        },
        "consumer_inventory_algorithm": consumer_inventory_algorithm_contract(),
        "consumer_inventory_reconciliation": {
            "candidate_identity_set_equals_fresh_preflight_identity_set": True,
            "candidate_runtime_required_set_equals_fresh_derived_preflight_set": True,
            "duplicate_consumer_ids_rejected": True,
            "fresh_consumers_may_not_be_omitted": True,
            "invented_consumers_rejected": True,
            "runtime_trace_consumer_ids_must_be_known_runtime_required_ids": True,
            "runtime_trace_identity_set_equals_runtime_required_identity_set": True,
            "nonruntime_rows_remain_present_and_typed": True,
            "baseline_changed_paths_require_changed_delta_rows": True,
            "candidate_local_expected_count_forbidden": True,
            "preflight_inventory_mutation_after_source_manifest_rejected": True,
            "independent_review_rescans_instead_of_trusting_execution_inventory": True,
        },
        "execution_preflight_attestation_contract": {
            "generated_before_source_manifest_and_candidate_generation": True,
            "binds": [
                "EXACT_GIT_COMMIT_AND_TREE",
                "SOURCE_REGISTRY_IDENTITY",
                "REVIEWED_V2_CONTRACT_IDENTITY",
                "SCHEMA_AND_PROTOCOL_IDENTITIES",
                "AUTHORIZED_IMPLEMENTATION_INVENTORY",
                "FRESH_REPOSITORY_CONSUMER_INVENTORY",
                "ALL_AND_RUNTIME_REQUIRED_IDENTITY_ROOTS_AND_COUNTS",
                "NONRUNTIME_COUNT",
                "PATH_LEVEL_BASELINE_DELTA_ROOT",
            ],
            "historical_counts_as_const_or_minimum": False,
            "candidate_input_used": False,
        },
        "source_manifest_contract": {
            "binds_preflight_attestation": True,
            "binds_accepted_v2_review": True,
            "binds_reviewed_v2_contract": True,
            "binds_registry_schemas_protocol_and_implementation": True,
            "binds_later_runtime_artifacts": False,
            "generated_after_successful_preflight": True,
            "immutable_before_candidate_generation": True,
        },
        "reviewed_schema_hash_edge_table": {
            "edge_count": len(edge_table),
            "edge_row_keys": [
                "blocked_path_applicability",
                "complete_path_applicability",
                "containing_artifact_type",
                "containing_generation_ordinal",
                "containing_generation_phase",
                "containing_schema_id",
                "hash_semantics",
                "referenced_artifact_type",
                "referenced_generation_ordinal",
                "referenced_generation_phase",
                "required_optional_status",
                "schema_field_path",
                "target_resolver",
            ],
            "rows": edge_table,
            "root_sha256": _edge_table_root(edge_table),
            "schema_walker_keywords": [
                "properties",
                "items",
                "prefixItems",
                "oneOf",
                "allOf",
                "anyOf",
            ],
            "array_path_token": "*",
            "any_unreviewed_64_hex_schema_leaf_is_rejected": True,
        },
        "generation_phase_table": {
            "rows": _phase_table(),
            "strictly_earlier_target_required_for_every_hash_edge": True,
            "artifact_generation_ordinal_unique_within_lifecycle_ledger": True,
            "generation_prerequisites_are_not_invented_as_content_hash_edges": True,
        },
        "schema_derived_graph_validation": {
            "derived_topological_order": topological_order,
            "declared_table_must_equal_schema_derived_table": True,
            "instance_edges_must_equal_schema_and_reviewed_table": True,
            "required_artifact_node_occurs_once_per_branch": True,
            "self_edges_rejected": True,
            "reciprocal_edges_rejected": True,
            "long_cycles_rejected": True,
            "earlier_phase_may_not_reference_later_phase": True,
            "complete_and_blocked_subgraphs_validated_separately": True,
            "topological_sort_required": True,
        },
        "runtime_schemas": schemas,
        "runtime_schema_count": len(schemas),
        "lifecycle_contract": {
            "PREFLIGHT_BLOCKED": {
                "prototype_root_created": False,
                "candidate_artifacts_created": False,
                "source_manifest_created": False,
                "exit_code": 2,
                "diagnostic_max_bytes": 16384,
                "bounded_diagnostic_only": True,
                "stage_a_authorized": False,
            },
            "COMPLETE": {
                "schema_validated_document_count": (
                    len(complete["schema_names"])
                    - 1
                    + complete["history_record_count"]
                ),
                "material_artifact_count": (
                    len(complete["artifact_bytes"])
                    - 1
                    + complete["history_shard_count"]
                ),
                "generation_node_count": len(complete["generation_ledger"]),
                "physical_generation_ledger": complete[
                    "artifact_generation_ledger"
                ],
                "candidate_file_count": len(
                    complete["documents"]["RUNTIME_MANIFEST"]
                    ["candidate_artifacts"]
                ),
                "history_record_count": complete["history_record_count"],
                "history_shard_count": complete["history_shard_count"],
                "generation_ledger": complete["generation_ledger"],
                "fixture_root_sha256": _fixture_root(complete),
                "positive_model_valid": True,
                "independent_review_required": True,
                "stage_b_authorized": False,
            },
            "POST_GENERATION_BLOCKED": {
                "schema_validated_document_count": (
                    len(blocked["schema_names"])
                    - 1
                    + blocked["history_record_count"]
                ),
                "material_artifact_count": (
                    len(blocked["artifact_bytes"])
                    - 1
                    + blocked["history_shard_count"]
                ),
                "generation_node_count": len(blocked["generation_ledger"]),
                "physical_generation_ledger": blocked[
                    "artifact_generation_ledger"
                ],
                "candidate_file_count": len(
                    blocked["documents"]["RUNTIME_MANIFEST"]
                    ["candidate_artifacts"]
                ),
                "history_record_count": blocked["history_record_count"],
                "history_shard_count": blocked["history_shard_count"],
                "generation_ledger": blocked["generation_ledger"],
                "fixture_root_sha256": _fixture_root(blocked),
                "positive_model_valid": True,
                "candidate_evidence_preserved": True,
                "runtime_report_terminal_chain_preserved": True,
                "independent_review_decision": "B_BLOCKED",
                "stage_b_authorized": False,
            },
            "PRE_FINALIZATION_GENERATION_FAILURE": {
                "canonical_runtime_report_terminal_claim_permitted": False,
                "partial_workspace_and_bounded_diagnostic_only": True,
                "nonexistent_artifact_hashes_required": False,
            },
        },
        "stage_a_control_contract": {
            "existing_preterminal_control_count": 76,
            "existing_preterminal_control_count_changed": False,
            "primary_control_count": 51,
            "readiness_control_count": 7,
            "runtime_contract_control_count": 18,
            "exact_control_ids": stage_a_ids,
            "exact_control_id_root_sha256": sha256(
                "\n".join(stage_a_ids).encode("utf-8")
            ),
            "exact_control_profiles": stage_a_profiles,
            "exact_control_profile_root_sha256": v1._control_profile_root(
                stage_a_profiles
            ),
            "retained_v1_successor_regression_count": 12,
            "new_v2_regression_count": 15,
            "permanent_successor_regression_count": 27,
            "permanent_successor_regression_results": controls,
            "permanent_successor_regression_results_root_sha256": (
                _permanent_control_results_root(controls)
            ),
            "successor_regressions_outside_preterminal_76_controls": True,
        },
        "consumer_inventory_historical_evidence": {
            "baseline": {
                "baseline_commit": "f9168ab5f566fb2019b9e76e68ff3e60e5c0dc52",
                "path_count": 496,
                "runtime_required_path_count": 470,
                "nonruntime_path_count": 26,
            },
            "accepted_v1_review_scan": {
                **reviewed_scan,
                "evidence_commit": SOURCE_COMMIT,
                "evidence_artifact": V1_REVIEW_REL,
            },
            "v2_preparation_source_scan": {
                **source_scan,
                "evidence_only_not_future_expectation": True,
            },
            "v2_preparation_callsite_scan": {
                "source_commit": SOURCE_COMMIT,
                "consumer_identity_count": complete["documents"]
                ["PREFLIGHT_CONSUMER_INVENTORY"]
                ["consumer_identity_count"],
                "unique_path_count": complete["documents"]
                ["PREFLIGHT_CONSUMER_INVENTORY"]
                ["unique_path_count"],
                "runtime_required_count": complete["documents"]
                ["PREFLIGHT_CONSUMER_INVENTORY"]
                ["runtime_required_count"],
                "nonruntime_count": complete["documents"]
                ["PREFLIGHT_CONSUMER_INVENTORY"]
                ["nonruntime_count"],
                "identity_root_sha256": complete["documents"]
                ["PREFLIGHT_CONSUMER_INVENTORY"]
                ["consumer_identity_root_sha256"],
                "evidence_only_not_future_expectation": True,
            },
            "counts_are_path_level_not_v2_callsite_identity_counts": True,
            "future_execution_uses_fresh_preflight_counts": True,
            "no_historical_count_is_normative_for_future_execution": True,
        },
        "implementation_path_contract": {
            "future_implementation_path_count": 4,
            "future_implementation_paths": AUTHORIZED_IMPLEMENTATION_PATHS,
            "implementation_changes_authorized_by_preparation": False,
            "independent_acceptance_required_before_any_implementation_change": True,
            "execution_scanner_and_validator_reconciliation_must_be_independent": True,
            "blocked_v0_implementation_not_amended": True,
        },
        "source_commit_layout": {
            "implementation_paths_present": {
                path: _git_path_exists(SOURCE_COMMIT, path)
                for path in AUTHORIZED_IMPLEMENTATION_PATHS
            },
            "production_and_prototype_paths_absent": {
                path: not _git_path_exists(SOURCE_COMMIT, path)
                for path in PRODUCTION_LAYOUT_PATHS
            },
        },
        "nonpromotion": {
            "consumer_cutover_performed": False,
            "current_projection_authoritative": False,
            "maintenance_target": MAINTENANCE_TARGET,
            "monolith_remains_authoritative_and_unchanged": True,
            "pillar_or_seam_claim_changed": False,
            "prototype_artifacts_created": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "stage_a_execution_performed": False,
            "stage_b_authorized": False,
            "unit_ledger_executed": False,
        },
        "supersession": {
            "preserves_v1_preparation_and_blocked_review": True,
            "v1_artifacts_amended_or_replaced": False,
            "effective_only_after_v2_independent_acceptance": True,
            "reason": (
                "ALIGN_ACTUAL_SCHEMA_GRAPH_GENERATION_ORDER_AND_EXTERNAL_"
                "REPOSITORY_CONSUMER_COMPLETENESS"
            ),
        },
        "validation_interpretation": (
            "focused preparation, review, authority, registry and exhaustive Lean "
            "validation passed; the combined predecessor invocation timed out, while "
            "its constituent suites subsequently passed independently; the full "
            "unbounded Python aggregate was not run; the repository is not described "
            "as universally green."
        ),
        "status": (
            "V2_SCHEMA_DERIVED_GRAPH_AND_REPOSITORY_PREFLIGHT_CONTRACT_PREPARED_"
            "INDEPENDENT_REVIEW_REQUIRED_STAGE_A_AND_STAGE_B_UNAUTHORIZED"
        ),
    }


_FINAL_CONTRACT_CACHE: dict[str, Any] | None = None


def build_contract() -> dict[str, Any]:
    global _FINAL_CONTRACT_CACHE
    if _FINAL_CONTRACT_CACHE is None:
        _FINAL_CONTRACT_CACHE = deepcopy(_build_contract_uncached())
    return deepcopy(_FINAL_CONTRACT_CACHE)


def build_packet(contract_raw: bytes | None = None) -> dict[str, Any]:
    if contract_raw is None:
        contract_raw = canonical_json_bytes(build_contract())
    return {
        "authorization": {
            "implementation_change_authorized": False,
            "independent_review_required": True,
            "maintenance_target_rotation_authorized": False,
            "prototype_execution_authorized": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_target_rotation_authorized": False,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "boundary": {
            "candidate_artifacts_created": False,
            "consumer_migration_started": False,
            "legacy_monolith_modified_or_retired": False,
            "prototype_execution_attempted": False,
            "scientific_artifacts_or_claims_changed": False,
            "terminal_execution_envelope_created": False,
            "v1_preparation_or_blocked_review_amended": False,
            "v2_contract_prepared_only": True,
        },
        "captured_at_utc": CAPTURED_AT_UTC,
        "contract_bundle": {"path": CONTRACT_REL, "sha256": sha256(contract_raw)},
        "counts": {
            "existing_stage_a_control_count": 76,
            "retained_v1_regression_count": 12,
            "new_v2_regression_count": 15,
            "permanent_successor_regression_count": 27,
            "runtime_schema_count": len(build_runtime_schemas()),
        },
        "execution_target_recommended_not_selected": EXECUTION_TARGET,
        "maintenance_target": MAINTENANCE_TARGET,
        "packet_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
            "PACKET_20260712_v2"
        ),
        "packet_target": PACKET_TARGET,
        "review_target_recommended_not_selected": REVIEW_TARGET,
        "scientific_target": SCIENTIFIC_TARGET,
        "source_commit": SOURCE_COMMIT,
        "status": (
            "V2_SUCCESSOR_PREPARED_SCHEMA_DERIVED_GRAPH_AND_FRESH_REPOSITORY_"
            "PREFLIGHT_INDEPENDENT_REVIEW_REQUIRED_NO_STAGE_A_OR_STAGE_B"
        ),
    }


def build_all() -> dict[Path, bytes]:
    contract = canonical_json_bytes(build_contract())
    packet = canonical_json_bytes(build_packet(contract))
    return {CONTRACT_PATH: contract, PACKET_PATH: packet}


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
        delete=False,
    ) as handle:
        temporary = Path(handle.name)
        handle.write(raw)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = build_all()
    if args.write:
        for path, raw in outputs.items():
            _atomic_write(path, raw)
        return 0
    mismatches = [
        path.relative_to(REPO_ROOT).as_posix()
        for path, raw in outputs.items()
        if not path.exists() or path.read_bytes() != raw
    ]
    if mismatches:
        raise V2PreparationError(
            "generated v2 artifacts differ: " + ", ".join(mismatches)
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
