"""Read-only access to a Stage-A loop-control registry prototype.

This module deliberately has no production-registry fallback and exposes no
write entry point.  Every public operation receives the prototype run root
explicitly.  Candidate JSON is parsed with duplicate-key and non-finite-number
rejection, checked against the externally reviewed v3 closed schemas, and
bound to the identities carried by the candidate projection/index/anchors.

The module is a reader, not an authority surface.  Its results do not select a
target, migrate a consumer, or make the prototype authoritative.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from functools import lru_cache
import base64
import binascii
import copy
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
from typing import Any, Final
import zlib

from jsonschema import Draft202012Validator, FormatChecker


JsonValue = (
    None | bool | int | float | str | list["JsonValue"] | dict[str, "JsonValue"]
)
ReviewedAnchors = Mapping[str, Any]

_REPO_ROOT: Final = Path(__file__).resolve().parents[3]
_SCHEMA_BUNDLE_RELPATH: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3.json"
)
_SCHEMA_BUNDLE_SHA256: Final = (
    "86289bf922d60c3320f040779a6043cdb3f2acf3d5393ce7503ef9d3375f6cde"
)
_EXECUTION_CONTRACT_RELPATH: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v0.json"
)
_EXECUTION_CONTRACT_SHA256: Final = (
    "272279d414591b25b3a519d22d92659f4a662ce1c9cbd5fadf3067f1eaa8f0bb"
)
_PROJECTION_RELPATH: Final = "projection/LOOP_CONTROL_CURRENT_v1.prototype.json"
_INDEX_RELPATH: Final = "history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json"
_CUSTODY_MANIFEST_RELPATH: Final = (
    "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1.json"
)
_CUSTODY_PAYLOAD_RELPATH: Final = "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz"
_ANCHORS_RELPATH: Final = "authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json"
_CONSUMER_SOURCE_MAP_RELPATH: Final = (
    "consumers/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2.json"
)

_SOURCE_REGISTRY_PATH: Final = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
_SOURCE_REGISTRY_COMMIT: Final = "f9168ab5f566fb2019b9e76e68ff3e60e5c0dc52"
_SOURCE_REGISTRY_GIT_BLOB: Final = "e6c5b3773dccd92fde9c0a8d486a56f993d6b235"
_SOURCE_REGISTRY_SHA256: Final = (
    "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
)
_SOURCE_REGISTRY_SIZE: Final = 52_340_650
_EXPECTED_RECORD_COUNT: Final = 4_691
_EXPECTED_RECORD_ROOT: Final = (
    "67a23fda6348a2a6e12e4c2af775d115c692ecbe4d0650f0844a982d869e112d"
)
_EXPECTED_IDENTITY_PAYLOAD_POINTER_ROOT: Final = (
    "a97799ea412006dde3c259b718b10aad9dee7012181611f3f1d5f1a1e821a967"
)
_EXPECTED_POINTER_ROOT: Final = (
    "219f4bc866b731b74ef50a439b6a869d8add33c6c5ce8e83a621115c1649c6bf"
)
_EXPECTED_AUTHORITY_COMMITMENT: Final = (
    "fd4348411236648d6216900eced59524b87c561bfa0d36186cf4c4d19a2e6b34"
)
_EXPECTED_SCIENTIFIC_TARGET: Final = "execute_pillar_seam_unit_mapping_ledger_v0"
_EXPECTED_MAINTENANCE_TARGET: Final = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
_MAX_PROJECTION_BYTES: Final = 1_048_576 - 1
_MAX_INDEX_BYTES: Final = 5_242_880
_MAX_SHARD_BYTES: Final = 5_242_880
_MAX_PAYLOAD_BYTES: Final = 2_124_270
_RECORD_ID = re.compile(r"^lcr1:[0-9a-f]{64}$")
_SHARD_PATH = re.compile(r"^history/shards/LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$")


class RegistryV1Error(ValueError):
    """Base class for fail-closed prototype reader errors."""


class RegistryFormatError(RegistryV1Error):
    """An artifact is not strict canonical JSON/JSONL or violates its schema."""


class RegistryIntegrityError(RegistryV1Error):
    """An artifact identity, cross-document binding, or custody check failed."""


class RegistryPathError(RegistryIntegrityError):
    """A candidate path is unsafe, escapes the run root, or is not canonical."""


class RegistryRecordNotFoundError(RegistryV1Error, KeyError):
    """The requested current or historical record does not exist."""


class AmbiguousRegistryRecordIdError(RegistryV1Error):
    """More than one shard or row claims the requested historical record ID."""


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _reject_constant(value: str) -> Any:
    raise RegistryFormatError(f"non-finite JSON constant rejected: {value}")


def _pairs_object(pairs: list[tuple[str, JsonValue]]) -> dict[str, JsonValue]:
    result: dict[str, JsonValue] = {}
    for key, value in pairs:
        if key in result:
            raise RegistryFormatError(f"duplicate JSON key rejected: {key}")
        result[key] = value
    return result


def _parse_json(raw: bytes, *, artifact: str) -> JsonValue:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise RegistryFormatError(f"{artifact}: UTF-8 BOM is prohibited")
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise RegistryFormatError(f"{artifact}: invalid UTF-8") from exc
    try:
        return json.loads(
            text,
            object_pairs_hook=_pairs_object,
            parse_constant=_reject_constant,
        )
    except RegistryFormatError:
        raise
    except (json.JSONDecodeError, ValueError) as exc:
        raise RegistryFormatError(f"{artifact}: invalid JSON: {exc}") from exc


def _canonical_json_bytes(value: JsonValue) -> bytes:
    try:
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
    except (TypeError, ValueError) as exc:
        raise RegistryFormatError("value cannot be represented as canonical JSON") from exc


def _compact_json_bytes(value: JsonValue) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise RegistryFormatError("value cannot be represented as compact canonical JSON") from exc


def _strict_document(raw: bytes, *, artifact: str, maximum_bytes: int) -> JsonValue:
    if not raw:
        raise RegistryFormatError(f"{artifact}: empty JSON document")
    if len(raw) > maximum_bytes:
        raise RegistryFormatError(
            f"{artifact}: {len(raw)} bytes exceeds the {maximum_bytes}-byte reader limit"
        )
    if b"\r" in raw:
        raise RegistryFormatError(f"{artifact}: CR/CRLF line endings are prohibited")
    if not raw.endswith(b"\n") or raw.endswith(b"\n\n"):
        raise RegistryFormatError(f"{artifact}: exactly one terminal LF is required")
    value = _parse_json(raw, artifact=artifact)
    if _canonical_json_bytes(value) != raw:
        raise RegistryFormatError(f"{artifact}: noncanonical JSON serialization")
    return value


@lru_cache(maxsize=1)
def _closed_schemas() -> dict[str, dict[str, Any]]:
    path = _REPO_ROOT / _SCHEMA_BUNDLE_RELPATH
    raw = path.read_bytes()
    if _sha256(raw) != _SCHEMA_BUNDLE_SHA256:
        raise RegistryIntegrityError("externally reviewed v3 schema bundle hash mismatch")
    value = _parse_json(raw, artifact=_SCHEMA_BUNDLE_RELPATH)
    if not isinstance(value, dict) or not isinstance(value.get("schemas"), dict):
        raise RegistryFormatError("v3 schema bundle has no closed schemas map")
    schemas = dict(value["schemas"])
    contract_path = _REPO_ROOT / _EXECUTION_CONTRACT_RELPATH
    contract_raw = contract_path.read_bytes()
    if _sha256(contract_raw) != _EXECUTION_CONTRACT_SHA256:
        raise RegistryIntegrityError("reviewed Stage-A execution contract hash mismatch")
    contract = _parse_json(contract_raw, artifact=_EXECUTION_CONTRACT_RELPATH)
    if not isinstance(contract, dict) or not isinstance(contract.get("runtime_schemas"), dict):
        raise RegistryFormatError("Stage-A execution contract has no runtime schemas map")
    overlap = set(schemas).intersection(contract["runtime_schemas"])
    if overlap:
        raise RegistryIntegrityError(
            f"Stage-A runtime schemas unexpectedly replace v3 schemas: {sorted(overlap)}"
        )
    schemas.update(contract["runtime_schemas"])
    Draft202012Validator.check_schema(schemas["current_projection"])
    return schemas


def _validate_schema(value: JsonValue, schema_name: str, artifact: str) -> None:
    schema = _closed_schemas().get(schema_name)
    if not isinstance(schema, dict):
        raise RegistryIntegrityError(f"reviewed schema missing: {schema_name}")
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    errors = sorted(validator.iter_errors(value), key=lambda error: list(error.absolute_path))
    if errors:
        error = errors[0]
        pointer = "".join(f"/{part}" for part in error.absolute_path)
        raise RegistryFormatError(f"{artifact}{pointer}: {error.message}")


def _candidate_root(candidate_root: Path) -> Path:
    root = Path(candidate_root)
    try:
        resolved = root.resolve(strict=True)
    except OSError as exc:
        raise RegistryPathError(f"candidate root is missing or inaccessible: {root}") from exc
    if not resolved.is_dir():
        raise RegistryPathError(f"candidate root is not a directory: {root}")
    return resolved


def _canonical_relative_path(relative: str) -> PurePosixPath:
    if not isinstance(relative, str) or not relative or "\\" in relative:
        raise RegistryPathError("candidate artifact path must be a nonempty POSIX path")
    path = PurePosixPath(relative)
    if path.is_absolute() or str(path) != relative:
        raise RegistryPathError(f"noncanonical candidate artifact path: {relative!r}")
    if any(part in {"", ".", ".."} for part in path.parts):
        raise RegistryPathError(f"unsafe candidate artifact path: {relative!r}")
    return path


def _artifact_path(root: Path, relative: str) -> Path:
    pure = _canonical_relative_path(relative)
    unresolved = root.joinpath(*pure.parts)
    try:
        resolved = unresolved.resolve(strict=True)
    except OSError as exc:
        raise RegistryPathError(f"candidate artifact is missing: {relative}") from exc
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise RegistryPathError(f"candidate artifact escapes the run root: {relative}") from exc
    if not resolved.is_file():
        raise RegistryPathError(f"candidate artifact is not a regular file: {relative}")
    return resolved


def _read_document(
    root: Path,
    relative: str,
    schema_name: str,
    maximum_bytes: int = _MAX_INDEX_BYTES,
) -> tuple[dict[str, Any], bytes]:
    raw = _artifact_path(root, relative).read_bytes()
    value = _strict_document(raw, artifact=relative, maximum_bytes=maximum_bytes)
    if not isinstance(value, dict):
        raise RegistryFormatError(f"{relative}: JSON document must be an object")
    _validate_schema(value, schema_name, relative)
    return value, raw


def _anchor_mapping(anchors: object) -> Mapping[str, Any]:
    if isinstance(anchors, Mapping):
        return anchors
    for attribute in ("payload", "data", "document"):
        value = getattr(anchors, attribute, None)
        if isinstance(value, Mapping):
            return value
    raise RegistryIntegrityError("reviewed anchors must be a mapping or expose a mapping payload")


def _load_anchors(root: Path, anchors: object | None) -> dict[str, Any]:
    candidate, _ = _read_document(
        root, _ANCHORS_RELPATH, "reviewed_trust_anchors", maximum_bytes=1_048_576
    )
    if anchors is not None and dict(_anchor_mapping(anchors)) != candidate:
        raise RegistryIntegrityError(
            "candidate reviewed-trust-anchors differ from supplied anchors"
        )
    source = candidate.get("source_registry")
    if not isinstance(source, dict):
        raise RegistryIntegrityError("reviewed anchors omit source_registry")
    expected = {
        "source_commit": _SOURCE_REGISTRY_COMMIT,
        "path": _SOURCE_REGISTRY_PATH,
        "git_blob": _SOURCE_REGISTRY_GIT_BLOB,
        "sha256": _SOURCE_REGISTRY_SHA256,
        "size_bytes": _SOURCE_REGISTRY_SIZE,
    }
    for key, value in expected.items():
        if source.get(key) != value:
            raise RegistryIntegrityError(f"reviewed source-registry anchor mismatch: {key}")
    if candidate.get("candidate_supplied_values_authoritative") is not False:
        raise RegistryIntegrityError("candidate-supplied trust values may not be authoritative")
    return candidate


def _source_identity(document: Mapping[str, Any], field: str) -> Mapping[str, Any]:
    identity = document.get(field)
    if not isinstance(identity, Mapping):
        raise RegistryIntegrityError(f"missing source identity: {field}")
    expected = {
        "source_commit": _SOURCE_REGISTRY_COMMIT,
        "path": _SOURCE_REGISTRY_PATH,
        "git_blob": _SOURCE_REGISTRY_GIT_BLOB,
        "sha256": _SOURCE_REGISTRY_SHA256,
        "size_bytes": _SOURCE_REGISTRY_SIZE,
    }
    for key, value in expected.items():
        if identity.get(key) != value:
            raise RegistryIntegrityError(f"{field}.{key} does not match reviewed legacy identity")
    return identity


def _load_projection_and_index(
    candidate_root: Path, anchors: object | None
) -> tuple[Path, dict[str, Any], dict[str, Any], dict[str, Any]]:
    root = _candidate_root(candidate_root)
    reviewed = _load_anchors(root, anchors)
    projection, _ = _read_document(
        root, _PROJECTION_RELPATH, "current_projection", _MAX_PROJECTION_BYTES
    )
    pointer = projection.get("history_index_pointer")
    if not isinstance(pointer, dict) or pointer.get("path") != _INDEX_RELPATH:
        raise RegistryIntegrityError(
            "projection history index pointer is not the canonical prototype path"
        )
    index, index_raw = _read_document(root, _INDEX_RELPATH, "history_index")
    if pointer.get("sha256") != _sha256(index_raw):
        raise RegistryIntegrityError("projection history-index pointer hash mismatch")
    _source_identity(projection, "source_legacy_identity")
    _source_identity(index, "source_registry_identity")
    if projection["scientific_authority"]["current_target"] != _EXPECTED_SCIENTIFIC_TARGET:
        raise RegistryIntegrityError("scientific current target differs from reviewed authority")
    if (
        projection["scientific_authority"]["authority_commitment_sha256"]
        != _EXPECTED_AUTHORITY_COMMITMENT
    ):
        raise RegistryIntegrityError("scientific authority commitment differs from reviewed root")
    if (
        projection["maintenance_authority"]["current_maintenance_target"]
        != _EXPECTED_MAINTENANCE_TARGET
    ):
        raise RegistryIntegrityError("maintenance target differs from reviewed authority")
    return root, projection, index, reviewed


def _payload_kind(value: JsonValue) -> str:
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
    if isinstance(value, dict):
        return "OBJECT"
    raise RegistryFormatError("unsupported history payload type")


def _validate_history_record(record: dict[str, Any], artifact: str) -> JsonValue:
    _validate_schema(record, "history_shard_record", artifact)
    encoded = record["payload_canonical_json_utf8_base64"]
    try:
        decoded = base64.b64decode(encoded, validate=True)
    except (binascii.Error, ValueError) as exc:
        raise RegistryFormatError(f"{artifact}: invalid strict RFC4648 base64 payload") from exc
    if base64.b64encode(decoded).decode("ascii") != encoded:
        raise RegistryFormatError(f"{artifact}: noncanonical base64 payload")
    if len(decoded) > _MAX_PAYLOAD_BYTES or len(decoded) != record["payload_size_bytes"]:
        raise RegistryIntegrityError(f"{artifact}: payload size mismatch")
    if _sha256(decoded) != record["payload_sha256"]:
        raise RegistryIntegrityError(f"{artifact}: payload hash mismatch")
    payload = _parse_json(decoded, artifact=f"{artifact} payload")
    if _compact_json_bytes(payload) != decoded:
        raise RegistryFormatError(f"{artifact}: payload is not compact canonical JSON")
    if _payload_kind(payload) != record["payload_kind"]:
        raise RegistryIntegrityError(f"{artifact}: payload kind mismatch")

    preimage: dict[str, JsonValue] = {
        "domain": "LOOP_CONTROL_RECORD_ID_v1",
        "record_class": record["record_class"],
        "source_path": record["source_path"],
        "source_git_blob": record["source_git_blob"],
        "logical_key": record["logical_key"],
        "original_json_pointer": record["original_json_pointer"],
        "payload_sha256": record["payload_sha256"],
        "identical_occurrence_ordinal": record["identical_occurrence_ordinal"],
    }
    expected_id = "lcr1:" + _sha256(_compact_json_bytes(preimage))
    if record["record_id"] != expected_id:
        raise RegistryIntegrityError(f"{artifact}: record ID does not bind its payload envelope")
    return payload


def _strict_shard_records(raw: bytes, *, artifact: str) -> list[dict[str, Any]]:
    if not raw or len(raw) > _MAX_SHARD_BYTES:
        raise RegistryFormatError(f"{artifact}: empty or oversized history shard")
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw:
        raise RegistryFormatError(f"{artifact}: BOM or CR/CRLF is prohibited")
    if not raw.endswith(b"\n") or raw.endswith(b"\n\n"):
        raise RegistryFormatError(f"{artifact}: each line requires exactly one LF")
    records: list[dict[str, Any]] = []
    previous_id: str | None = None
    for number, line in enumerate(raw[:-1].split(b"\n"), start=1):
        if not line:
            raise RegistryFormatError(f"{artifact}:{number}: empty JSONL line")
        value = _parse_json(line, artifact=f"{artifact}:{number}")
        if not isinstance(value, dict):
            raise RegistryFormatError(f"{artifact}:{number}: history row must be an object")
        if _compact_json_bytes(value) != line:
            raise RegistryFormatError(f"{artifact}:{number}: noncanonical JSONL row")
        _validate_history_record(value, f"{artifact}:{number}")
        record_id = value["record_id"]
        if previous_id is not None and record_id <= previous_id:
            if record_id == previous_id:
                raise AmbiguousRegistryRecordIdError(
                    f"duplicate record ID in {artifact}: {record_id}"
                )
            raise RegistryIntegrityError(f"{artifact}: record IDs are not strictly sorted")
        previous_id = record_id
        records.append(value)
    return records


def _shard_id(descriptor: Mapping[str, Any]) -> str:
    preimage: dict[str, JsonValue] = {
        "domain": "LOOP_CONTROL_SHARD_ID_v1",
        "sequence_index": descriptor["sequence_index"],
        "path": descriptor["path"],
        "first_record_id": descriptor["first_record_id"],
        "last_record_id": descriptor["last_record_id"],
        "record_count": descriptor["record_count"],
        "record_id_root_sha256": descriptor["record_id_root_sha256"],
        "sha256": descriptor["sha256"],
        "uncompressed_size_bytes": descriptor["uncompressed_size_bytes"],
    }
    return "lcs1:" + _sha256(_compact_json_bytes(preimage))


def _load_shard(
    root: Path, descriptor: Mapping[str, Any]
) -> tuple[list[dict[str, Any]], bytes]:
    relative = descriptor.get("path")
    if not isinstance(relative, str) or not _SHARD_PATH.fullmatch(relative):
        raise RegistryPathError("history index contains a noncanonical shard path")
    raw = _artifact_path(root, relative).read_bytes()
    if len(raw) != descriptor.get("uncompressed_size_bytes"):
        raise RegistryIntegrityError(f"{relative}: shard size differs from its index row")
    if _sha256(raw) != descriptor.get("sha256"):
        raise RegistryIntegrityError(f"{relative}: shard hash differs from its index row")
    records = _strict_shard_records(raw, artifact=relative)
    ids = [record["record_id"] for record in records]
    if not ids:
        raise RegistryIntegrityError(f"{relative}: empty shard")
    if descriptor.get("record_count") != len(ids):
        raise RegistryIntegrityError(f"{relative}: record count differs from its index row")
    if descriptor.get("first_record_id") != ids[0] or descriptor.get("last_record_id") != ids[-1]:
        raise RegistryIntegrityError(f"{relative}: record range differs from its index row")
    record_root = _sha256("\n".join(ids).encode("utf-8"))
    if descriptor.get("record_id_root_sha256") != record_root:
        raise RegistryIntegrityError(f"{relative}: record-ID root differs from its index row")
    if descriptor.get("shard_id") != _shard_id(descriptor):
        raise RegistryIntegrityError(f"{relative}: shard ID is not bound to its descriptor")
    return records, raw


def _index_shards(index: Mapping[str, Any]) -> list[dict[str, Any]]:
    shards = index.get("shards")
    if not isinstance(shards, list) or not all(isinstance(row, dict) for row in shards):
        raise RegistryIntegrityError("history index has no valid shards array")
    if index.get("shard_count") != len(shards):
        raise RegistryIntegrityError("history index shard_count mismatch")
    expected_sequences = list(range(len(shards)))
    if [row.get("sequence_index") for row in shards] != expected_sequences:
        raise RegistryIntegrityError("history shard sequence is not contiguous from zero")
    paths = [row.get("path") for row in shards]
    ids = [row.get("shard_id") for row in shards]
    if len(set(paths)) != len(paths) or len(set(ids)) != len(ids):
        raise RegistryIntegrityError("history index contains duplicate shard path or ID")
    previous_last: str | None = None
    for expected_sequence, descriptor in enumerate(shards):
        expected_path = (
            f"history/shards/LOOP_CONTROL_HISTORY_{expected_sequence:04d}.jsonl"
        )
        if descriptor.get("path") != expected_path:
            raise RegistryIntegrityError(
                f"history shard path does not match sequence {expected_sequence:04d}"
            )
        first = descriptor.get("first_record_id")
        last = descriptor.get("last_record_id")
        if not isinstance(first, str) or not isinstance(last, str) or first > last:
            raise RegistryIntegrityError("history index has an invalid shard range")
        if previous_last is not None and first <= previous_last:
            raise AmbiguousRegistryRecordIdError(
                "history index ranges overlap or are out of order"
            )
        previous_last = last
    return shards


def load_current_projection(
    candidate_root: Path, anchors: object | None = None
) -> dict[str, Any]:
    """Load and validate the non-authoritative current projection."""

    _, projection, _, _ = _load_projection_and_index(candidate_root, anchors)
    return copy.deepcopy(projection)


def get_current_target(candidate_root: Path, anchors: object | None = None) -> str:
    """Return the prototype projection's reviewed scientific target token."""

    projection = load_current_projection(candidate_root, anchors)
    return str(projection["scientific_authority"]["current_target"])


def get_current_maintenance_target(
    candidate_root: Path, anchors: object | None = None
) -> str:
    """Return the prototype projection's reviewed maintenance target token."""

    projection = load_current_projection(candidate_root, anchors)
    return str(projection["maintenance_authority"]["current_maintenance_target"])


def get_current_workstream(
    candidate_root: Path, workstream_id: str, anchors: object | None = None
) -> dict[str, Any]:
    """Return the one active projected workstream, or fail distinctly if absent."""

    projection = load_current_projection(candidate_root, anchors)
    row = projection["active_scientific_workstream"]
    if row["workstream_id"] != workstream_id:
        raise RegistryRecordNotFoundError(f"current workstream not found: {workstream_id}")
    return copy.deepcopy(row)


def get_historical_record(
    candidate_root: Path, record_id: str, anchors: object | None = None
) -> dict[str, Any]:
    """Load one historical envelope using only its index-selected shard."""

    if not isinstance(record_id, str) or not _RECORD_ID.fullmatch(record_id):
        raise RegistryRecordNotFoundError(f"invalid or missing historical record ID: {record_id!r}")
    root, _, index, _ = _load_projection_and_index(candidate_root, anchors)
    candidates = [
        row
        for row in _index_shards(index)
        if row["first_record_id"] <= record_id <= row["last_record_id"]
    ]
    if not candidates:
        raise RegistryRecordNotFoundError(f"historical record not found: {record_id}")
    if len(candidates) != 1:
        raise AmbiguousRegistryRecordIdError(
            f"historical record falls in {len(candidates)} shard ranges: {record_id}"
        )
    records, _ = _load_shard(root, candidates[0])
    matches = [row for row in records if row["record_id"] == record_id]
    if not matches:
        raise RegistryRecordNotFoundError(f"historical record not found: {record_id}")
    if len(matches) != 1:
        raise AmbiguousRegistryRecordIdError(f"duplicate historical record: {record_id}")
    return copy.deepcopy(matches[0])


def iter_historical_records(
    candidate_root: Path,
    anchors: object | None = None,
    *,
    start_record_id: str | None = None,
    end_record_id: str | None = None,
    record_class: str | None = None,
) -> Iterator[dict[str, Any]]:
    """Iterate validated history rows, optionally narrowing ID range/class."""

    for boundary in (start_record_id, end_record_id):
        if boundary is not None and not _RECORD_ID.fullmatch(boundary):
            raise RegistryRecordNotFoundError(f"invalid historical range boundary: {boundary!r}")
    if (
        start_record_id is not None
        and end_record_id is not None
        and start_record_id > end_record_id
    ):
        raise RegistryV1Error("start_record_id must not exceed end_record_id")
    if record_class not in {None, "ROOT_FIELD", "WORKSTREAM"}:
        raise RegistryV1Error(f"unsupported record_class filter: {record_class!r}")
    root, _, index, _ = _load_projection_and_index(candidate_root, anchors)
    for descriptor in _index_shards(index):
        if start_record_id is not None and descriptor["last_record_id"] < start_record_id:
            continue
        if end_record_id is not None and descriptor["first_record_id"] > end_record_id:
            continue
        records, _ = _load_shard(root, descriptor)
        for record in records:
            record_id = record["record_id"]
            if start_record_id is not None and record_id < start_record_id:
                continue
            if end_record_id is not None and record_id > end_record_id:
                continue
            if record_class is not None and record["record_class"] != record_class:
                continue
            yield copy.deepcopy(record)


def reconstruct_legacy_registry(
    candidate_root: Path, anchors: object | None = None
) -> bytes:
    """Return byte-exact legacy bytes from the bounded custody payload."""

    root, _, index, _ = _load_projection_and_index(candidate_root, anchors)
    manifest, _ = _read_document(
        root, _CUSTODY_MANIFEST_RELPATH, "legacy_byte_custody_manifest"
    )
    _source_identity(manifest, "source_identity")
    custody_pointer = index["custody_manifest_pointer"]
    manifest_raw = _artifact_path(root, _CUSTODY_MANIFEST_RELPATH).read_bytes()
    if (
        custody_pointer["path"] != _CUSTODY_MANIFEST_RELPATH
        or custody_pointer["sha256"] != _sha256(manifest_raw)
        or custody_pointer["schema_id"] != manifest["schema_id"]
        or manifest["payload_identity"]["path"] != _CUSTODY_PAYLOAD_RELPATH
        or manifest["gzip_profile"]["path"] != _CUSTODY_PAYLOAD_RELPATH
    ):
        raise RegistryIntegrityError("custody manifest points outside the canonical payload path")
    raw = _artifact_path(root, _CUSTODY_PAYLOAD_RELPATH).read_bytes()
    identity = manifest["payload_identity"]
    if (
        len(raw) != identity["compressed_size_bytes"]
        or _sha256(raw) != identity["compressed_sha256"]
    ):
        raise RegistryIntegrityError("custody payload compressed identity mismatch")
    if len(raw) < 18 or raw[:3] != b"\x1f\x8b\x08":
        raise RegistryIntegrityError("custody payload is not an RFC1952 DEFLATE member")
    if raw[3] != 0 or raw[4:8] != b"\x00\x00\x00\x00" or raw[8] != 2 or raw[9] != 255:
        raise RegistryIntegrityError("custody payload gzip header profile mismatch")
    decompressor = zlib.decompressobj(wbits=31)
    try:
        reconstructed = decompressor.decompress(raw, _SOURCE_REGISTRY_SIZE + 1)
    except zlib.error as exc:
        raise RegistryIntegrityError("custody payload decompression failed") from exc
    if decompressor.unconsumed_tail:
        raise RegistryIntegrityError("custody reconstruction exceeds its reviewed size bound")
    try:
        reconstructed += decompressor.flush()
    except zlib.error as exc:
        raise RegistryIntegrityError("custody payload finalization failed") from exc
    if (
        not decompressor.eof
        or decompressor.unused_data
        or decompressor.unconsumed_tail
        or len(reconstructed) != _SOURCE_REGISTRY_SIZE
        or _sha256(reconstructed) != _SOURCE_REGISTRY_SHA256
    ):
        raise RegistryIntegrityError(
            "custody reconstruction is not byte-exact or has trailing data"
        )
    requirement = manifest["reconstruction_requirement"]
    if (
        requirement["byte_identical"] is not True
        or requirement["decompressed_size_bytes"] != len(reconstructed)
        or requirement["decompressed_sha256"] != _sha256(reconstructed)
    ):
        raise RegistryIntegrityError("custody manifest reconstruction requirement mismatch")
    return reconstructed


def verify_registry_integrity(
    candidate_root: Path, anchors: object | None = None
) -> dict[str, Any]:
    """Verify the complete read-only projection/index/shard/custody candidate."""

    root, _, index, _ = _load_projection_and_index(candidate_root, anchors)
    shards = _index_shards(index)
    ids: list[str] = []
    pointer_payload_rows: list[str] = []
    pointers: list[str] = []
    root_field_count = 0
    workstream_count = 0
    shard_sizes: list[int] = []
    first_line_sizes: list[int] = []
    for descriptor in shards:
        shard_records, shard_raw = _load_shard(root, descriptor)
        for row in shard_records:
            ids.append(row["record_id"])
            pointer_payload_rows.append(
                f'{row["record_id"]}:{row["payload_sha256"]}:{row["original_json_pointer"]}'
            )
            pointers.append(row["original_json_pointer"])
            root_field_count += row["record_class"] == "ROOT_FIELD"
            workstream_count += row["record_class"] == "WORKSTREAM"
        shard_sizes.append(len(shard_raw))
        first_line_sizes.append(len(_compact_json_bytes(shard_records[0])) + 1)
        del shard_records
    for preceding_size, following_first_line in zip(shard_sizes, first_line_sizes[1:]):
        if preceding_size + following_first_line <= _MAX_SHARD_BYTES:
            raise RegistryIntegrityError("history shards do not use reviewed greedy packing")
    if (
        len(ids) != _EXPECTED_RECORD_COUNT
        or index["record_accounting"]["total_record_count"] != len(ids)
    ):
        raise RegistryIntegrityError("complete history record count mismatch")
    if ids != sorted(ids) or len(set(ids)) != len(ids):
        raise RegistryIntegrityError("complete history record ID set is not unique and sorted")
    record_root = _sha256("\n".join(ids).encode("utf-8"))
    payload_pointer_root = _sha256(
        "\n".join(sorted(pointer_payload_rows)).encode("utf-8")
    )
    pointer_root = _sha256("\n".join(sorted(pointers)).encode("utf-8"))
    accounting = index["record_accounting"]
    if (
        accounting["root_field_record_count"] != root_field_count
        or accounting["workstream_record_count"] != workstream_count
    ):
        raise RegistryIntegrityError("history record-class accounting mismatch")
    roots = {
        "full_record_identity_root_sha256": (record_root, _EXPECTED_RECORD_ROOT),
        "identity_payload_pointer_root_sha256": (
            payload_pointer_root,
            _EXPECTED_IDENTITY_PAYLOAD_POINTER_ROOT,
        ),
        "original_pointer_set_sha256": (pointer_root, _EXPECTED_POINTER_ROOT),
    }
    for field, (observed, externally_reviewed) in roots.items():
        if accounting[field] != observed or observed != externally_reviewed:
            raise RegistryIntegrityError(f"complete history root mismatch: {field}")
    consumer_pointer = index["consumer_source_map_pointer"]
    consumer_map, consumer_raw = _read_document(
        root, _CONSUMER_SOURCE_MAP_RELPATH, "consumer_source_map", 8_388_608
    )
    if (
        consumer_pointer["path"] != _CONSUMER_SOURCE_MAP_RELPATH
        or consumer_pointer["sha256"] != _sha256(consumer_raw)
        or consumer_pointer["schema_id"] != consumer_map["schema_id"]
    ):
        raise RegistryIntegrityError("consumer source-map pointer identity mismatch")
    reconstructed = reconstruct_legacy_registry(root, anchors)
    return {
        "passed": True,
        "read_only": True,
        "candidate_root": str(root),
        "shard_count": len(shards),
        "record_count": len(records),
        "record_identity_root_sha256": record_root,
        "legacy_registry_sha256": _sha256(reconstructed),
        "legacy_registry_size_bytes": len(reconstructed),
    }


__all__ = [
    "AmbiguousRegistryRecordIdError",
    "RegistryFormatError",
    "RegistryIntegrityError",
    "RegistryPathError",
    "RegistryRecordNotFoundError",
    "RegistryV1Error",
    "get_current_maintenance_target",
    "get_current_target",
    "get_current_workstream",
    "get_historical_record",
    "iter_historical_records",
    "load_current_projection",
    "reconstruct_legacy_registry",
    "verify_registry_integrity",
]
