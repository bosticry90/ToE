"""Fail-closed validator for the loop-control registry v1 Stage-A prototype.

This module implements only the read-only, pre-cutover surface authorized by
``LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET``.  It
never edits the legacy registry, authority surfaces, consumers, or history
shards.  Stage B and the cutover-only controls NC-044 and RC-001 are
deliberately unavailable.

The reviewed schema and protocol bundles remain the source of truth.  Loading
them at runtime is intentional: copying 20 closed schemas into Python would
create a second, drift-prone specification.
"""

from __future__ import annotations

import base64
import binascii
import copy
import gzip
import hashlib
import io
import json
import os
import re
import struct
import subprocess
import zlib
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, BinaryIO, Iterable, Iterator, Mapping, MutableMapping, Sequence

from jsonschema import Draft202012Validator, FormatChecker


JsonValue = Any
ArtifactKind = str
WriterProbe = Mapping[str, Any]
ShadowTraceManifest = Mapping[str, Any]
ReviewedTrustAnchors = Mapping[str, Any]
ReviewedStageAAcceptance = Mapping[str, Any]

_REPO_ROOT = Path(__file__).resolve().parents[3]
_RELEASE = _REPO_ROOT / "formal" / "docs" / "release"
_V3_SCHEMA_PATH = _RELEASE / "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3.json"
_V3_PROTOCOL_PATH = _RELEASE / "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v3.json"
_EXECUTION_CONTRACT_PATH = _RELEASE / "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_BUNDLE_20260711_v0.json"
_PACKET_REVIEW_PATH = "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_INDEPENDENT_REVIEW_20260711_v0.json"
_PACKET_PATH = "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_20260711_v0.json"
_SOURCE_REGISTRY_PATH = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
_PROTOTYPE_BASE = "formal/scratch/loop_control_registry_v1_prototype"

SOURCE_REGISTRY_SHA256 = "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
SOURCE_REGISTRY_SIZE = 52_340_650
SOURCE_REGISTRY_GIT_BLOB = "e6c5b3773dccd92fde9c0a8d486a56f993d6b235"
SOURCE_REGISTRY_COMMIT = "f9168ab5f566fb2019b9e76e68ff3e60e5c0dc52"
V3_ACCEPTANCE_COMMIT = "6e4d1e11b1953b9712588464b31c12047555189c"
V1_AUTHORITY_ROOT = "fd4348411236648d6216900eced59524b87c561bfa0d36186cf4c4d19a2e6b34"
V1_RECORD_ID_ROOT = "67a23fda6348a2a6e12e4c2af775d115c692ecbe4d0650f0844a982d869e112d"
V1_PAYLOAD_POINTER_ROOT = "a97799ea412006dde3c259b718b10aad9dee7012181611f3f1d5f1a1e821a967"
V1_POINTER_ROOT = "219f4bc866b731b74ef50a439b6a869d8add33c6c5ce8e83a621115c1649c6bf"
BASELINE_CONSUMER_MAP_SHA256 = "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642"
EXPECTED_HISTORICAL_RECORDS = 4_691
EXPECTED_BASELINE_CONSUMERS = 496
MAX_PROJECTION_BYTES = 1_048_576
MAX_SHARD_BYTES = 5 * 1_048_576
MAX_HISTORY_PAYLOAD_BYTES = 2_124_270

RUN_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$")
ARTIFACT_RELPATH_RE = re.compile(
    r"^(?!/)(?!.*//)(?![.]{1,2}(?:/|$))(?!.*(?:/[.]{1,2})(?:/|$))"
    r"[A-Za-z0-9_-](?:[A-Za-z0-9._-]*[A-Za-z0-9_-])?"
    r"(?:/[A-Za-z0-9_-](?:[A-Za-z0-9._-]*[A-Za-z0-9_-])?)*$"
)
REPOSITORY_RELPATH_RE = re.compile(
    r'^(?!/)(?!.*//)(?![.]{1,2}(?:/|$))(?!.*(?:/[.]{1,2})(?:/|$))'
    r'(?!.*[\\:\x00-\x1f*?<>|\"])(?![^/]*[. ](?:/|$))'
    r'(?!.*[/][^/]*[. ](?:/|$))[^/]+(?:/[^/]+)*$'
)
SHARD_RE = re.compile(r"^history/shards/LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
GIT_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")

_FIXED_KIND_BY_PATH = {
    "authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json": "REVIEWED_TRUST_ANCHORS",
    "compat/LOOP_CONTROL_LEGACY_RECONSTRUCTION_RESULT_v1.json": "RECONSTRUCTION_RESULT",
    "compat/LOOP_CONTROL_REGISTRY_v0.reconstructed.json": "COMPATIBILITY_RECONSTRUCTION",
    "consumers/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2.json": "CONSUMER_SOURCE_MAP",
    "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1.json": "CUSTODY_MANIFEST",
    "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz": "CUSTODY_PAYLOAD",
    "history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json": "HISTORY_INDEX",
    "manifests/LOOP_CONTROL_EXECUTION_PREFLIGHT_v1.json": "EXECUTION_PREFLIGHT",
    "manifests/LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v1.json": "RUNTIME_RUN_MANIFEST",
    "manifests/LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v1.json": "ROLLBACK_INVENTORY",
    "projection/LOOP_CONTROL_CURRENT_v1.prototype.json": "CURRENT_PROJECTION",
    "traces/LOOP_CONTROL_RUNTIME_SHADOW_TRACE_v1.jsonl": "RUNTIME_SHADOW_TRACE",
    "traces/LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v1.json": "RUNTIME_SHADOW_TRACE_MANIFEST",
    "validation/LOOP_CONTROL_CONTROL_HARNESS_REPORT_v1.json": "CONTROL_HARNESS_REPORT",
    "validation/LOOP_CONTROL_REGISTRY_V1_VALIDATION_REPORT.json": "VALIDATION_REPORT",
    "validation/LOOP_CONTROL_STAGE_A_PRECUTOVER_REPORT_v1.json": "STAGE_A_PRECUTOVER_REPORT",
    "validation/LOOP_CONTROL_STAGE_B_FULL_HARNESS_RESULT_v1.json": "STAGE_B_FULL_HARNESS_RESULT",
    "validation/LOOP_CONTROL_WRITER_PROBE_v1.json": "WRITER_PROBE",
}
_SOURCE_MANIFEST_REL = "manifests/LOOP_CONTROL_ARTIFACT_SOURCE_MANIFEST_v1.json"
_TRANSIENT_RECONSTRUCTION_REL = "compat/LOOP_CONTROL_REGISTRY_v0.reconstructed.json"
_CANDIDATE_KINDS = frozenset({"CURRENT_PROJECTION", "HISTORY_INDEX", "HISTORY_SHARD", "CUSTODY_PAYLOAD"})


class RegistryValidationError(ValueError):
    """A deterministic, typed fail-closed validation error."""

    def __init__(
        self,
        error_code: str,
        message: str,
        *,
        artifact_path: str = "validation/LOOP_CONTROL_REGISTRY_V1_VALIDATION_REPORT.json",
        json_pointer: str = "",
        control_id: str | None = None,
    ) -> None:
        super().__init__(message)
        self.error_code = error_code
        self.artifact_path = artifact_path
        self.json_pointer = json_pointer
        self.control_id = control_id

    def issue(self) -> dict[str, Any]:
        return {
            "artifact_path": self.artifact_path,
            "json_pointer": self.json_pointer,
            "message": str(self),
            "control_id": self.control_id,
            "error_code": self.error_code,
        }


class RegistryRecordNotFoundError(LookupError):
    pass


class AmbiguousRegistryRecordIdError(LookupError):
    pass


@dataclass(frozen=True)
class ArtifactRow:
    artifact_kind: str
    candidate_payload: bool
    path: str
    sha256: str
    size_bytes: int

    def as_dict(self) -> dict[str, Any]:
        return {
            "artifact_kind": self.artifact_kind,
            "candidate_payload": self.candidate_payload,
            "path": self.path,
            "sha256": self.sha256,
            "size_bytes": self.size_bytes,
        }


@dataclass(frozen=True)
class ArtifactSource:
    candidate_root: Path
    exact_run_root: Path
    run_id: str
    manifest: Mapping[str, Any]
    artifacts: tuple[ArtifactRow, ...]
    files: Mapping[str, bytes]
    candidate_tree_sha256: str
    inventory_sha256: str


@dataclass(frozen=True)
class RuntimeContractReport:
    passed: bool
    error_code: str | None
    issues: tuple[Mapping[str, Any], ...]

    def as_dict(self) -> dict[str, Any]:
        return {"passed": self.passed, "error_code": self.error_code, "issues": [dict(x) for x in self.issues]}


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _reject_constant(value: str) -> None:
    raise RegistryValidationError("V1-E-JSON-NONFINITE", f"non-finite JSON constant is forbidden: {value}")


def _reject_duplicate_pairs(pairs: Sequence[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RegistryValidationError("V1-E-JSON-KEY-DUPLICATE", f"duplicate JSON key: {key}")
        result[key] = value
    return result


def strict_load_json(raw: bytes, artifact_kind: ArtifactKind = "JSON") -> JsonValue:
    """Parse strict UTF-8 JSON, rejecting BOM, duplicate keys, and nonfinite values."""

    if raw.startswith(b"\xef\xbb\xbf"):
        raise RegistryValidationError("V1-E-UTF8-BOM", f"{artifact_kind} starts with a UTF-8 BOM")
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise RegistryValidationError("V1-E-UTF8-INVALID", f"{artifact_kind} is not strict UTF-8") from exc
    try:
        return json.loads(text, object_pairs_hook=_reject_duplicate_pairs, parse_constant=_reject_constant)
    except RegistryValidationError:
        raise
    except json.JSONDecodeError as exc:
        raise RegistryValidationError("V1-E-JSONL-NONCANONICAL", f"invalid {artifact_kind} JSON: {exc.msg}") from exc


def _canonical_compact(value: Any) -> bytes:
    try:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise RegistryValidationError("V1-E-JSON-NONFINITE", "value is not finite canonical JSON") from exc


def canonical_artifact_bytes(value: Any) -> bytes:
    try:
        return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False) + "\n").encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise RegistryValidationError("V1-E-JSON-NONFINITE", "value is not finite canonical JSON") from exc


def strict_iter_jsonl(stream: BinaryIO, maximum_bytes: int = MAX_SHARD_BYTES) -> Iterator[Mapping[str, Any]]:
    raw = stream.read(maximum_bytes + 1)
    if len(raw) > maximum_bytes:
        raise RegistryValidationError("V1-E-SHARD-SIZE", "JSONL stream exceeds its byte limit")
    if raw.startswith(b"\xef\xbb\xbf"):
        raise RegistryValidationError("V1-E-UTF8-BOM", "JSONL starts with a UTF-8 BOM")
    if b"\r" in raw:
        raise RegistryValidationError("V1-E-JSONL-CRLF", "JSONL must use LF only")
    if not raw:
        raise RegistryValidationError("V1-E-SHARD-EMPTY", "history shard is empty")
    if not raw.endswith(b"\n"):
        raise RegistryValidationError("V1-E-TERMINAL-NEWLINE", "JSONL must end with exactly one LF")
    lines = raw[:-1].split(b"\n")
    if any(line == b"" for line in lines):
        raise RegistryValidationError("V1-E-JSONL-BLANK", "JSONL contains a blank line")
    for line in lines:
        value = strict_load_json(line, "HISTORY_SHARD_RECORD")
        if not isinstance(value, dict) or _canonical_compact(value) != line:
            raise RegistryValidationError("V1-E-JSONL-NONCANONICAL", "JSONL record is not compact canonical JSON")
        yield value


def _load_reviewed_json(path: Path) -> Mapping[str, Any]:
    value = strict_load_json(path.read_bytes(), path.name)
    if not isinstance(value, dict):
        raise RegistryValidationError("V1-E-RUNTIME-SCHEMA", f"{path.name} must contain an object")
    return value


_V3_SCHEMA_BUNDLE = _load_reviewed_json(_V3_SCHEMA_PATH)
_V3_PROTOCOL = _load_reviewed_json(_V3_PROTOCOL_PATH)
_EXECUTION_CONTRACT = _load_reviewed_json(_EXECUTION_CONTRACT_PATH)
_V3_SCHEMAS: Mapping[str, Mapping[str, Any]] = _V3_SCHEMA_BUNDLE["schemas"]
_RUNTIME_SCHEMAS: Mapping[str, Mapping[str, Any]] = _EXECUTION_CONTRACT["runtime_schemas"]
_CONTROL_ERROR_MAP: Mapping[str, str] = _EXECUTION_CONTRACT["control_harness_contract"]["control_error_map"]
_STAGE_A = _EXECUTION_CONTRACT["lifecycle"]["stage_a_precutover_execution_after_separate_authorization"]
STAGE_A_CONTROL_IDS: tuple[str, ...] = tuple(_STAGE_A["control_result_order"])
STAGE_A_PRIMARY_IDS: tuple[str, ...] = tuple(_STAGE_A["primary_control_ids"])
STAGE_A_READINESS_IDS: tuple[str, ...] = tuple(_STAGE_A["readiness_control_ids"])
STAGE_A_RUNTIME_IDS: tuple[str, ...] = tuple(
    row["control_id"] for row in _EXECUTION_CONTRACT["runtime_validator_contract"]["negative_controls"]
)
STAGE_A_EXCLUDED_IDS = frozenset(_STAGE_A["cutover_control_ids_excluded"])

if len(STAGE_A_PRIMARY_IDS) != 51 or len(STAGE_A_READINESS_IDS) != 7 or len(STAGE_A_RUNTIME_IDS) != 18:
    raise RuntimeError("reviewed Stage-A control cardinalities drifted")
if len(STAGE_A_CONTROL_IDS) != 58 or STAGE_A_EXCLUDED_IDS != {
    "REGISTRY-V1-NC-044",
    "REGISTRY-READINESS-V1-RC-001",
}:
    raise RuntimeError("reviewed Stage-A cutover exclusions drifted")


def _schema_error_pointer(error: Any) -> str:
    if not error.absolute_path:
        return ""
    def esc(item: Any) -> str:
        return str(item).replace("~", "~0").replace("/", "~1")
    return "/" + "/".join(esc(item) for item in error.absolute_path)


def _validate_schema(payload: Any, schema: Mapping[str, Any], *, code: str, artifact_path: str) -> None:
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    errors = sorted(validator.iter_errors(payload), key=lambda e: (list(e.absolute_path), e.message))
    if errors:
        error = errors[0]
        raise RegistryValidationError(
            code,
            error.message,
            artifact_path=artifact_path,
            json_pointer=_schema_error_pointer(error),
        )


def _canonical_domain_root(domain: str, rows: Iterable[bytes]) -> str:
    joined = b"\n".join(rows)
    return _sha256(domain.encode("utf-8") + b"\0" + joined)


def _plain_root(values: Iterable[str]) -> str:
    return _sha256("\n".join(values).encode("utf-8"))


def _validate_artifact_relpath(value: str) -> None:
    if not isinstance(value, str) or not ARTIFACT_RELPATH_RE.fullmatch(value):
        raise RegistryValidationError("V1-E-PATH-TRAVERSAL", f"invalid prototype artifact relative path: {value!r}")


def _validate_repository_relpath(value: str) -> None:
    if not isinstance(value, str) or not REPOSITORY_RELPATH_RE.fullmatch(value):
        raise RegistryValidationError("V1-E-PATH-TRAVERSAL", f"invalid repository relative path: {value!r}")


def _ensure_safe_candidate_root(candidate_root: Path) -> tuple[Path, str]:
    root = candidate_root.resolve(strict=True)
    base = (_REPO_ROOT / _PROTOTYPE_BASE).resolve(strict=True)
    try:
        rel = root.relative_to(base)
    except ValueError as exc:
        raise RegistryValidationError("V1-E-PATH-TRAVERSAL", "candidate root is outside the fixed prototype base") from exc
    if len(rel.parts) != 1 or not RUN_ID_RE.fullmatch(rel.parts[0]):
        raise RegistryValidationError("V1-E-PATH-TRAVERSAL", "candidate root must be exactly one validated run-id below the prototype base")
    for ancestor in (base, root):
        if ancestor.is_symlink():
            raise RegistryValidationError("V1-E-PATH-TRAVERSAL", "prototype ancestors may not be links")
    return root, rel.parts[0]


def _artifact_kind_for_path(path: str) -> str | None:
    if SHARD_RE.fullmatch(path):
        return "HISTORY_SHARD"
    return _FIXED_KIND_BY_PATH.get(path)


def _derive_inventory_roots(rows: Sequence[ArtifactRow]) -> tuple[str, str]:
    sorted_rows = sorted(rows, key=lambda row: row.path.encode("utf-8"))
    encoded = [_canonical_compact(row.as_dict()) for row in sorted_rows]
    inventory = _canonical_domain_root("LOOP_CONTROL_RUN_ARTIFACT_INVENTORY_ROOT_v1", encoded)
    candidate = _canonical_domain_root(
        "LOOP_CONTROL_CANDIDATE_PAYLOAD_TREE_ROOT_v1",
        [_canonical_compact(row.as_dict()) for row in sorted_rows if row.candidate_payload],
    )
    return inventory, candidate


def resolve_artifact_source(
    candidate_root: Path,
    exact_run_root: Path | None = None,
    expected_tree_sha256: str | None = None,
) -> ArtifactSource:
    """Resolve and hash-bind a candidate tree without trusting candidate flags."""

    root, run_id = _ensure_safe_candidate_root(Path(candidate_root))
    if exact_run_root is not None and root != Path(exact_run_root).resolve(strict=True):
        raise RegistryValidationError("V1-E-PATH-TRAVERSAL", "candidate root differs from the exact run root")
    manifest_path = root / _SOURCE_MANIFEST_REL
    manifest = strict_load_json(manifest_path.read_bytes(), "ARTIFACT_SOURCE_MANIFEST")
    if not isinstance(manifest, dict):
        raise RegistryValidationError("V1-E-RUNTIME-SCHEMA", "artifact source manifest must be an object")
    _validate_schema(manifest, _RUNTIME_SCHEMAS["artifact_source_manifest"], code="V1-E-RUNTIME-SCHEMA", artifact_path=_SOURCE_MANIFEST_REL)
    if manifest["run_id"] != run_id or manifest["run_root_repo_relative"] != f"{_PROTOTYPE_BASE}/{run_id}":
        raise RegistryValidationError("V1-E-RUNTIME-CROSS-DOCUMENT", "artifact manifest run root is inconsistent")

    regular_files: dict[str, bytes] = {}
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        if path.is_symlink():
            raise RegistryValidationError("V1-E-PATH-TRAVERSAL", "candidate artifacts may not be symbolic links")
        rel = path.relative_to(root).as_posix()
        _validate_artifact_relpath(rel)
        if rel != _SOURCE_MANIFEST_REL and rel != _TRANSIENT_RECONSTRUCTION_REL:
            regular_files[rel] = path.read_bytes()

    manifest_rows = manifest.get("artifacts", [])
    if len({row.get("path") for row in manifest_rows if isinstance(row, dict)}) != len(manifest_rows):
        raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", "artifact paths must be unique")
    rows: list[ArtifactRow] = []
    for raw_row in manifest_rows:
        if not isinstance(raw_row, dict):
            raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", "artifact row must be an object")
        path = raw_row["path"]
        _validate_artifact_relpath(path)
        expected_kind = _artifact_kind_for_path(path)
        if expected_kind is None or raw_row["artifact_kind"] != expected_kind:
            raise RegistryValidationError("V1-E-ARTIFACT-KIND-PATH", f"artifact kind does not match path: {path}")
        candidate_payload = expected_kind in _CANDIDATE_KINDS
        if raw_row["candidate_payload"] is not candidate_payload:
            raise RegistryValidationError("V1-E-ARTIFACT-KIND-PATH", f"candidate payload flag is invalid: {path}")
        if path not in regular_files:
            raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", f"inventoried artifact is missing: {path}")
        raw = regular_files[path]
        if raw_row["sha256"] != _sha256(raw) or raw_row["size_bytes"] != len(raw):
            raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", f"artifact identity mismatch: {path}")
        rows.append(ArtifactRow(expected_kind, candidate_payload, path, _sha256(raw), len(raw)))
    if set(regular_files) != {row.path for row in rows}:
        raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", "regular run-root artifacts are not inventoried exactly once")

    inventory, candidate = _derive_inventory_roots(rows)
    if manifest["inventory_sha256"] != inventory:
        raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", "inventory root does not match actual artifacts")
    if manifest["candidate_tree_sha256"] != candidate:
        raise RegistryValidationError("V1-E-CANDIDATE-TREE", "candidate tree root does not match actual candidate payload")
    if expected_tree_sha256 is not None and candidate != expected_tree_sha256:
        raise RegistryValidationError("V1-E-CANDIDATE-TREE", "candidate tree differs from the externally expected root")
    candidate_count = sum(row.candidate_payload for row in rows)
    if manifest["candidate_payload_artifact_count"] != candidate_count or manifest["evidence_artifact_count"] != len(rows) - candidate_count:
        raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", "artifact category counts are inconsistent")
    return ArtifactSource(root, root, run_id, manifest, tuple(rows), regular_files, candidate, inventory)


def _git_bytes(commit: str, path: str) -> bytes:
    if not GIT_COMMIT_RE.fullmatch(commit):
        raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "invalid Git commit identity")
    completed = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=_REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RegistryValidationError(
            "V1-E-TRUST-ANCHOR-EXTERNAL-BINDING",
            f"reviewed Git object is unavailable: {commit}:{path}",
        )
    return completed.stdout


def _git_is_ancestor(ancestor: str, descendant: str) -> bool:
    if not GIT_COMMIT_RE.fullmatch(ancestor) or not GIT_COMMIT_RE.fullmatch(descendant):
        return False
    return subprocess.run(
        ["git", "merge-base", "--is-ancestor", ancestor, descendant],
        cwd=_REPO_ROOT,
        capture_output=True,
        check=False,
    ).returncode == 0


def load_reviewed_trust_anchors(review_commit: str, expected_sha256: str) -> Mapping[str, Any]:
    """Load Stage-A anchors from the independently reviewed Git object.

    The candidate tree never supplies the values used here.  Dynamic hashes and
    commits are copied only after the review object itself has been verified.
    """

    review_raw = _git_bytes(review_commit, _PACKET_REVIEW_PATH)
    if _sha256(review_raw) != expected_sha256:
        raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "packet review SHA-256 mismatch")
    review = strict_load_json(review_raw, "PACKET_INDEPENDENT_REVIEW")
    if not isinstance(review, dict):
        raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "packet review is not an object")
    auth = review.get("authorization", {})
    if (
        review.get("decision") != "ACCEPT_PREPARATION_AND_AUTHORIZE_ONLY_BOUNDED_STAGE_A_76_CONTROL_READ_ONLY_PROTOTYPE_IMPLEMENTATION_AND_EXECUTION"
        or auth.get("bounded_stage_a_read_only_prototype_execution_authorized") is not True
        or auth.get("stage_b_full_harness_authorized") is not False
    ):
        raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "review does not authorize bounded Stage A only")
    packet_commit = review.get("reviewed_commit")
    packet_sha = review.get("packet_sha256")
    if not isinstance(packet_commit, str) or not isinstance(packet_sha, str):
        raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "review packet binding is incomplete")
    packet_raw = _git_bytes(packet_commit, _PACKET_PATH)
    if _sha256(packet_raw) != packet_sha:
        raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "reviewed packet SHA-256 mismatch")
    if not _git_is_ancestor(packet_commit, review_commit):
        raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "reviewed packet is not an ancestor of review")

    anchors: dict[str, Any] = {
        "schema_id": "LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1",
        "v3_acceptance_commit": V3_ACCEPTANCE_COMMIT,
        "accepted_v3_review": {
            "path": "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_INDEPENDENT_REVIEW_20260711_v3.json",
            "sha256": "07353bc1c0d379518344aa16c25080fefb6dd9c1527cad4accb64216b15adae0",
            "reviewed_preparation_commit": "f9051af27988dd745bf39d28ae4d610973d5a029",
        },
        "v3_contract": {
            "packet_sha256": "90037c92d74f4ab18be82863dd240065bc5ebd312e5b8647b52f1b3a549cb216",
            "protocol_sha256": "ad65ceb56d3b284b3a55e433afc13745c3c574c9f2e7bf0fe367172924ea08e2",
            "schema_bundle_sha256": "86289bf922d60c3320f040779a6043cdb3f2acf3d5393ce7503ef9d3375f6cde",
        },
        "external_v1": {
            "source_commit": "6aba59d8d399b331db010f1f5f857075b9100b7f",
            "guardrail_sha256": "41994b0c1703d7f7f7ff7aeda217900a3136489f070ae55a88f2db10a13d12c0",
            "review_sha256": "4b99d6d3801a8bbd2f918311116dfdfce8ef595f7c0e1b629bc3595820612dca",
        },
        "source_registry": {
            "source_commit": SOURCE_REGISTRY_COMMIT,
            "path": _SOURCE_REGISTRY_PATH,
            "git_blob": SOURCE_REGISTRY_GIT_BLOB,
            "sha256": SOURCE_REGISTRY_SHA256,
            "size_bytes": SOURCE_REGISTRY_SIZE,
        },
        "authority_commitment_sha256": V1_AUTHORITY_ROOT,
        "requirements_lock_sha256": "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
        "prototype_execution_authorization": {
            "packet_path": _PACKET_PATH,
            "packet_sha256": packet_sha,
            "reviewed_packet_commit": packet_commit,
            "independent_review_path": _PACKET_REVIEW_PATH,
            "independent_review_sha256": expected_sha256,
            "authorization_review_commit": review_commit,
            "bounded_stage_a_authorized": True,
            "stage_b_authorized": False,
            "anchor_source": "GIT_COMMIT_VERIFIED_INDEPENDENT_REVIEW",
        },
        "candidate_supplied_values_authoritative": False,
    }
    _validate_schema(
        anchors,
        _RUNTIME_SCHEMAS["reviewed_trust_anchors"],
        code="V1-E-TRUST-ANCHOR-EXTERNAL-BINDING",
        artifact_path="authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json",
    )
    return anchors


def load_reviewed_stage_a_acceptance(review_commit: str, expected_sha256: str) -> Mapping[str, Any]:
    """Stage-B-only loader retained as a fail-closed interface boundary."""

    del review_commit, expected_sha256
    raise RegistryValidationError(
        "V1-E-STAGE-B-NOT-AUTHORIZED",
        "Stage B is not authorized by the Stage-A execution contract",
    )


def _trust_anchor_sha256(anchors: Mapping[str, Any]) -> str:
    _validate_schema(
        anchors,
        _RUNTIME_SCHEMAS["reviewed_trust_anchors"],
        code="V1-E-AUTHORITY-EXTERNAL-BINDING",
        artifact_path="authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json",
    )
    return _sha256(canonical_artifact_bytes(anchors))


def _require_identity(actual: Mapping[str, Any], expected: Mapping[str, Any], code: str, name: str) -> None:
    for key, value in expected.items():
        if actual.get(key) != value:
            raise RegistryValidationError(code, f"{name} identity differs at {key}")


def _load_source_json(source: ArtifactSource, rel: str, schema_name: str) -> Mapping[str, Any]:
    raw = source.files.get(rel)
    if raw is None:
        raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", f"required artifact is missing: {rel}", artifact_path=rel)
    value = strict_load_json(raw, schema_name.upper())
    if not isinstance(value, dict):
        raise RegistryValidationError("V1-E-NONCONTROL-DIAGNOSTIC", f"{schema_name} must be an object", artifact_path=rel)
    _validate_schema(value, _V3_SCHEMAS[schema_name], code="V1-E-NONCONTROL-DIAGNOSTIC", artifact_path=rel)
    if raw != canonical_artifact_bytes(value):
        raise RegistryValidationError("V1-E-JSONL-NONCANONICAL", f"{rel} is not canonical artifact JSON", artifact_path=rel)
    return value


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
    if isinstance(value, dict):
        return "OBJECT"
    raise RegistryValidationError("V1-E-HISTORY-PAYLOAD-ENVELOPE", "unsupported history payload type")


def validate_history_record_payload_contract(
    record: Mapping[str, Any],
    expected_source_path: str = _SOURCE_REGISTRY_PATH,
    expected_source_git_blob: str = SOURCE_REGISTRY_GIT_BLOB,
    expected_record_id: str | None = None,
    expected_payload_sha256: str | None = None,
) -> Mapping[str, Any]:
    _validate_schema(
        record,
        _V3_SCHEMAS["history_shard_record"],
        code="V1-E-SCHEMA-VERSION",
        artifact_path="history/shards/LOOP_CONTROL_HISTORY_0000.jsonl",
    )
    encoded = record["payload_canonical_json_utf8_base64"]
    try:
        decoded = base64.b64decode(encoded, validate=True)
    except (binascii.Error, ValueError) as exc:
        raise RegistryValidationError("V1-E-HISTORY-PAYLOAD-BASE64", "history payload is not strict RFC4648 base64") from exc
    if base64.b64encode(decoded).decode("ascii") != encoded:
        raise RegistryValidationError("V1-E-HISTORY-PAYLOAD-BASE64", "history payload base64 has noncanonical pad bits")
    if len(decoded) != record["payload_size_bytes"] or len(decoded) > MAX_HISTORY_PAYLOAD_BYTES:
        raise RegistryValidationError("V1-E-HISTORY-PAYLOAD-ENVELOPE", "history payload size does not match its envelope")
    if _sha256(decoded) != record["payload_sha256"]:
        raise RegistryValidationError("V1-E-HISTORY-PAYLOAD-ENVELOPE", "history payload SHA-256 does not match its envelope")
    parsed = strict_load_json(decoded, "HISTORY_PAYLOAD")
    if _canonical_compact(parsed) != decoded:
        raise RegistryValidationError("V1-E-HISTORY-PAYLOAD-CANONICAL-IDENTITY", "history payload is not compact canonical JSON")
    if _payload_kind(parsed) != record["payload_kind"]:
        raise RegistryValidationError("V1-E-HISTORY-PAYLOAD-ENVELOPE", "history payload kind does not match parsed JSON")
    if record["source_path"] != expected_source_path or record["source_git_blob"] != expected_source_git_blob:
        raise RegistryValidationError("V1-E-SOURCE-IDENTITY-DUPLICATE", "history source identity differs from reviewed source")
    preimage = {
        "domain": "LOOP_CONTROL_RECORD_ID_v1",
        "record_class": record["record_class"],
        "source_path": record["source_path"],
        "source_git_blob": record["source_git_blob"],
        "logical_key": record["logical_key"],
        "original_json_pointer": record["original_json_pointer"],
        "payload_sha256": record["payload_sha256"],
        "identical_occurrence_ordinal": record["identical_occurrence_ordinal"],
    }
    calculated = "lcr1:" + _sha256(_canonical_compact(preimage))
    if record["record_id"] != calculated:
        raise RegistryValidationError("V1-E-RECORD-ID-FORGED", "history record ID does not match its canonical preimage")
    if expected_record_id is not None and calculated != expected_record_id:
        raise RegistryValidationError("V1-E-RECORD-ID-AMBIGUOUS", "history record differs from expected record ID")
    if expected_payload_sha256 is not None and record["payload_sha256"] != expected_payload_sha256:
        raise RegistryValidationError("V1-E-HISTORY-EXTERNAL-ROOT", "history payload differs from external expected identity")
    return record


def _shard_id(row: Mapping[str, Any]) -> str:
    preimage = {
        "domain": "LOOP_CONTROL_SHARD_ID_v1",
        "sequence_index": row["sequence_index"],
        "path": row["path"],
        "first_record_id": row["first_record_id"],
        "last_record_id": row["last_record_id"],
        "record_count": row["record_count"],
        "record_id_root_sha256": row["record_id_root_sha256"],
        "sha256": row["sha256"],
        "uncompressed_size_bytes": row["uncompressed_size_bytes"],
    }
    return "lcs1:" + _sha256(_canonical_compact(preimage))


def _validate_projection(source: ArtifactSource, anchors: Mapping[str, Any]) -> Mapping[str, Any]:
    rel = "projection/LOOP_CONTROL_CURRENT_v1.prototype.json"
    raw = source.files.get(rel)
    if raw is None:
        raise RegistryValidationError("V1-E-PROJECTION-FIELD-MISSING", "current projection is missing", artifact_path=rel)
    if len(raw) >= MAX_PROJECTION_BYTES:
        raise RegistryValidationError("V1-E-PROJECTION-SIZE", "current projection is not below one MiB", artifact_path=rel)
    try:
        value = strict_load_json(raw, "CURRENT_PROJECTION")
    except RegistryValidationError:
        raise
    if not isinstance(value, dict):
        raise RegistryValidationError("V1-E-PROJECTION-FIELD-MISSING", "current projection must be an object", artifact_path=rel)
    schema = _V3_SCHEMAS["current_projection"]
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    errors = sorted(validator.iter_errors(value), key=lambda e: (list(e.absolute_path), e.validator, e.message))
    if errors:
        error = errors[0]
        code = "V1-E-PROJECTION-FIELD-EXTRA" if error.validator == "additionalProperties" else "V1-E-PROJECTION-FIELD-MISSING"
        raise RegistryValidationError(code, error.message, artifact_path=rel, json_pointer=_schema_error_pointer(error))
    if raw != canonical_artifact_bytes(value):
        raise RegistryValidationError("V1-E-JSONL-NONCANONICAL", "projection is not canonical artifact JSON", artifact_path=rel)
    sci = value["scientific_authority"]
    maint = value["maintenance_authority"]
    if sci["current_target"] != "execute_pillar_seam_unit_mapping_ledger_v0" or sci["authority_commitment_sha256"] != anchors["authority_commitment_sha256"]:
        raise RegistryValidationError("V1-E-AUTHORITY-EXTERNAL-BINDING", "scientific authority differs from external review", artifact_path=rel)
    if maint["current_maintenance_target"] != "prepare_loop_control_registry_sharding_and_current_projection_packet_v0":
        raise RegistryValidationError("V1-E-MAINTENANCE-TARGET-CARDINALITY", "maintenance target differs from reviewed authority", artifact_path=rel)
    if any(v != "no" for v in value["nonpromotion_assertions"].values()):
        raise RegistryValidationError("V1-E-NONPROMOTION-COMMITMENT", "a nonpromotion assertion was promoted", artifact_path=rel)
    source_identity = anchors["source_registry"]
    _require_identity(value["source_legacy_identity"], source_identity, "V1-E-AUTHORITY-EXTERNAL-BINDING", "projection source")
    return value


def _validate_history(source: ArtifactSource, anchors: Mapping[str, Any], projection: Mapping[str, Any]) -> tuple[Mapping[str, Any], tuple[Mapping[str, Any], ...]]:
    index_rel = "history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json"
    index = _load_source_json(source, index_rel, "history_index")
    source_identity = anchors["source_registry"]
    _require_identity(index["source_registry_identity"], source_identity, "V1-E-AUTHORITY-EXTERNAL-BINDING", "history source")
    if projection["history_index_pointer"]["path"] != index_rel or projection["history_index_pointer"]["sha256"] != _sha256(source.files[index_rel]):
        raise RegistryValidationError("V1-E-INDEX-POINTER", "projection history-index pointer does not bind the actual index", artifact_path=index_rel)
    accounting = index["record_accounting"]
    external_accounting = {
        "authority_commitment_sha256": V1_AUTHORITY_ROOT,
        "full_record_identity_root_sha256": V1_RECORD_ID_ROOT,
        "identity_payload_pointer_root_sha256": V1_PAYLOAD_POINTER_ROOT,
        "original_pointer_set_sha256": V1_POINTER_ROOT,
        "root_field_record_count": 4_152,
        "workstream_record_count": 539,
        "total_record_count": EXPECTED_HISTORICAL_RECORDS,
    }
    if accounting != external_accounting:
        raise RegistryValidationError("V1-E-HISTORY-EXTERNAL-ROOT", "history accounting differs from external reviewed roots", artifact_path=index_rel)
    shards = index["shards"]
    if index["shard_count"] != len(shards):
        raise RegistryValidationError("V1-E-SHARD-MISSING", "history shard count does not match the index", artifact_path=index_rel)
    if len({row["shard_id"] for row in shards}) != len(shards):
        raise RegistryValidationError("V1-E-SHARD-ID-DUPLICATE", "duplicate shard ID", artifact_path=index_rel)
    if len({row["path"] for row in shards}) != len(shards):
        raise RegistryValidationError("V1-E-SHARD-PATH-DUPLICATE", "duplicate shard path", artifact_path=index_rel)
    actual_shard_paths = sorted(path for path in source.files if SHARD_RE.fullmatch(path))
    indexed_paths = [row["path"] for row in shards]
    if set(actual_shard_paths) - set(indexed_paths):
        raise RegistryValidationError("V1-E-SHARD-EXTRA", "unindexed history shard exists", artifact_path=index_rel)
    if set(indexed_paths) - set(actual_shard_paths):
        raise RegistryValidationError("V1-E-SHARD-MISSING", "indexed history shard is missing", artifact_path=index_rel)
    if [row["sequence_index"] for row in shards] != list(range(len(shards))) or indexed_paths != [f"history/shards/LOOP_CONTROL_HISTORY_{i:04d}.jsonl" for i in range(len(shards))]:
        raise RegistryValidationError("V1-E-SHARD-ORDER", "history shards are not in canonical sequence order", artifact_path=index_rel)

    all_records: list[Mapping[str, Any]] = []
    previous_last: str | None = None
    for shard_row in shards:
        rel = shard_row["path"]
        raw = source.files[rel]
        if len(raw) > MAX_SHARD_BYTES or shard_row["uncompressed_size_bytes"] > MAX_SHARD_BYTES:
            raise RegistryValidationError("V1-E-SHARD-SIZE", "history shard exceeds five MiB", artifact_path=rel)
        if _sha256(raw) != shard_row["sha256"] or len(raw) != shard_row["uncompressed_size_bytes"]:
            raise RegistryValidationError("V1-E-SHARD-HASH", "history shard bytes do not match index", artifact_path=rel)
        records = list(strict_iter_jsonl(io.BytesIO(raw), MAX_SHARD_BYTES))
        for record in records:
            validate_history_record_payload_contract(record)
        ids = [record["record_id"] for record in records]
        if ids != sorted(ids):
            raise RegistryValidationError("V1-E-SHARD-ORDER", "record IDs are not sorted within shard", artifact_path=rel)
        if len(set(ids)) != len(ids):
            raise RegistryValidationError("V1-E-RECORD-ID-DUPLICATE", "duplicate record ID within shard", artifact_path=rel)
        if previous_last is not None and ids[0] <= previous_last:
            raise RegistryValidationError("V1-E-SHARD-RANGE-OVERLAP", "history shard ranges overlap or regress", artifact_path=rel)
        if shard_row["first_record_id"] != ids[0] or shard_row["last_record_id"] != ids[-1]:
            raise RegistryValidationError("V1-E-SHARD-RANGE-GAP", "history shard range metadata differs from records", artifact_path=rel)
        if shard_row["record_count"] != len(records) or shard_row["record_id_root_sha256"] != _plain_root(ids):
            raise RegistryValidationError("V1-E-RECORD-COUNT", "history shard record accounting differs", artifact_path=rel)
        if shard_row["shard_id"] != _shard_id(shard_row):
            raise RegistryValidationError("V1-E-SHARD-HASH", "history shard ID does not match its preimage", artifact_path=rel)
        previous_last = ids[-1]
        all_records.extend(records)
    record_ids = [record["record_id"] for record in all_records]
    if len(all_records) != EXPECTED_HISTORICAL_RECORDS:
        raise RegistryValidationError("V1-E-RECORD-COUNT", "complete history record count is not 4,691", artifact_path=index_rel)
    if len(set(record_ids)) != len(record_ids):
        raise RegistryValidationError("V1-E-RECORD-ID-DUPLICATE", "duplicate record ID across shards", artifact_path=index_rel)
    if _plain_root(sorted(record_ids)) != V1_RECORD_ID_ROOT:
        raise RegistryValidationError("V1-E-RECORD-MISSING", "complete history record root differs from external root", artifact_path=index_rel)
    pointers = sorted(record["original_json_pointer"] for record in all_records)
    if _plain_root(pointers) != V1_POINTER_ROOT:
        raise RegistryValidationError("V1-E-RECORD-EXTRA", "history pointer root differs from external root", artifact_path=index_rel)
    payload_pointer_rows = sorted(
        f"{record['record_id']}:{record['payload_sha256']}:{record['original_json_pointer']}" for record in all_records
    )
    if _plain_root(payload_pointer_rows) != V1_PAYLOAD_POINTER_ROOT:
        raise RegistryValidationError("V1-E-HISTORY-EXTERNAL-ROOT", "payload/pointer root differs from external root", artifact_path=index_rel)
    source_keys = [
        (record["record_class"], record["logical_key"], record["original_json_pointer"], record["identical_occurrence_ordinal"])
        for record in all_records
    ]
    if len(set(source_keys)) != len(source_keys):
        raise RegistryValidationError("V1-E-SOURCE-IDENTITY-DUPLICATE", "duplicate history source identity", artifact_path=index_rel)
    return index, tuple(all_records)


def _decompress_single_gzip(raw: bytes) -> bytes:
    if len(raw) < 18 or raw[:3] != b"\x1f\x8b\x08":
        raise RegistryValidationError("V1-E-CUSTODY-GZIP-HEADER", "custody payload is not RFC1952 DEFLATE")
    if raw[3] != 0 or raw[4:8] != b"\0\0\0\0" or raw[8] != 2 or raw[9] != 255:
        raise RegistryValidationError("V1-E-CUSTODY-GZIP-HEADER", "custody gzip header differs from frozen profile")
    decoder = zlib.decompressobj(wbits=16 + zlib.MAX_WBITS)
    try:
        decoded = decoder.decompress(raw, SOURCE_REGISTRY_SIZE + 1)
        decoded += decoder.flush()
    except zlib.error as exc:
        raise RegistryValidationError("V1-E-CUSTODY-HASH", "custody gzip stream failed validation") from exc
    if len(decoded) > SOURCE_REGISTRY_SIZE:
        raise RegistryValidationError("V1-E-CUSTODY-SIZE", "custody payload exceeds frozen decompressed size")
    if not decoder.eof:
        raise RegistryValidationError("V1-E-CUSTODY-HASH", "custody gzip member is incomplete")
    if decoder.unused_data:
        code = "V1-E-CUSTODY-GZIP-MULTIMEMBER" if decoder.unused_data.startswith(b"\x1f\x8b") else "V1-E-CUSTODY-GZIP-TRAILING"
        raise RegistryValidationError(code, "custody payload contains bytes after the single gzip member")
    return decoded


def _validate_custody(source: ArtifactSource, anchors: Mapping[str, Any], records: Sequence[Mapping[str, Any]]) -> Mapping[str, Any]:
    manifest_rel = "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1.json"
    payload_rel = "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz"
    result_rel = "compat/LOOP_CONTROL_LEGACY_RECONSTRUCTION_RESULT_v1.json"
    manifest = _load_source_json(source, manifest_rel, "legacy_byte_custody_manifest")
    _require_identity(manifest["source_identity"], anchors["source_registry"], "V1-E-AUTHORITY-EXTERNAL-BINDING", "custody source")
    payload = source.files.get(payload_rel)
    if payload is None:
        raise RegistryValidationError("V1-E-CUSTODY-HASH", "custody payload is missing", artifact_path=payload_rel)
    if manifest["payload_identity"]["path"] != payload_rel or manifest["payload_identity"]["compressed_sha256"] != _sha256(payload) or manifest["payload_identity"]["compressed_size_bytes"] != len(payload):
        raise RegistryValidationError("V1-E-CUSTODY-HASH", "custody payload identity differs from actual bytes", artifact_path=payload_rel)
    decoded = _decompress_single_gzip(payload)
    if len(decoded) != SOURCE_REGISTRY_SIZE:
        raise RegistryValidationError("V1-E-CUSTODY-SIZE", "custody bytes do not have the frozen source size", artifact_path=payload_rel)
    if _sha256(decoded) != SOURCE_REGISTRY_SHA256:
        raise RegistryValidationError("V1-E-CUSTODY-HASH", "custody bytes do not have the frozen source hash", artifact_path=payload_rel)
    source_json = strict_load_json(decoded, "CUSTODY_RECONSTRUCTED_LEGACY")
    if not isinstance(source_json, dict):
        raise RegistryValidationError("V1-E-CUSTODY-SEMANTIC-ROOT", "reconstructed legacy registry is not an object")
    # Byte custody is primary; the externally bound record roots independently
    # bind the history representation already validated above.
    if len(records) != EXPECTED_HISTORICAL_RECORDS:
        raise RegistryValidationError("V1-E-CUSTODY-SEMANTIC-ROOT", "custody and history accounting disagree")
    result = _load_source_json(source, result_rel, "compatibility_reconstruction_result")
    _require_identity(result["source_identity"], anchors["source_registry"], "V1-E-AUTHORITY-EXTERNAL-BINDING", "reconstruction source")
    if not all(result["byte_comparison"].values()) or not all(result["semantic_history_comparison"].values()):
        raise RegistryValidationError("V1-E-CUSTODY-SEMANTIC-ROOT", "reconstruction result does not establish byte and semantic identity")
    if result["reconstruction_identity"]["sha256"] != SOURCE_REGISTRY_SHA256 or result["reconstruction_identity"]["size_bytes"] != SOURCE_REGISTRY_SIZE:
        raise RegistryValidationError("V1-E-CUSTODY-HASH", "reconstruction result identity differs from frozen source")
    if result["cleanup"]["temporary_output_removed"] is not True or result["cleanup"]["runtime_output_retained"] is not False:
        raise RegistryValidationError("V1-E-CUSTODY-HASH", "temporary reconstruction was not removed")
    return manifest


def _coerce_mapping(value: Any, name: str) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    for attribute in ("payload", "data", "document"):
        candidate = getattr(value, attribute, None)
        if isinstance(candidate, Mapping):
            return candidate
    raise RegistryValidationError("V1-E-RUNTIME-SCHEMA", f"{name} must be a mapping")


def _validate_consumer_and_trace(
    source: ArtifactSource,
    trace_manifest_override: Mapping[str, Any] | None = None,
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    consumer_rel = "consumers/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2.json"
    trace_rel = "traces/LOOP_CONTROL_RUNTIME_SHADOW_TRACE_v1.jsonl"
    manifest_rel = "traces/LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v1.json"
    consumer_map = _load_source_json(source, consumer_rel, "consumer_source_map")
    if consumer_map["baseline"]["sha256"] != BASELINE_CONSUMER_MAP_SHA256 or consumer_map["baseline"]["consumer_count"] != EXPECTED_BASELINE_CONSUMERS:
        raise RegistryValidationError("V1-E-CONSUMER-UNCLASSIFIED", "consumer baseline differs from reviewed 496-row map", artifact_path=consumer_rel)
    consumers = consumer_map["consumers"]
    if consumer_map["current_scan"]["consumer_count"] != len(consumers):
        raise RegistryValidationError("V1-E-CONSUMER-UNCLASSIFIED", "consumer scan count differs from consumer rows", artifact_path=consumer_rel)
    if consumer_map["current_scan"]["unclassified_count"] != 0:
        raise RegistryValidationError("V1-E-CONSUMER-UNCLASSIFIED", "consumer scan contains unclassified paths", artifact_path=consumer_rel)
    if len({row["consumer_id"] for row in consumers}) != len(consumers) or len({row["path"] for row in consumers}) != len(consumers):
        raise RegistryValidationError("V1-E-CONSUMER-UNCLASSIFIED", "consumer source map contains duplicate identity or path", artifact_path=consumer_rel)
    if any(row["runtime_disposition"] == "PENDING" for row in consumers):
        raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "consumer source map retains pending runtime dispositions", artifact_path=consumer_rel)

    if trace_manifest_override is None:
        trace_manifest = _load_source_json(source, manifest_rel, "runtime_shadow_trace_manifest")
    else:
        trace_manifest = _coerce_mapping(trace_manifest_override, "trace_manifest")
        _validate_schema(
            trace_manifest,
            _V3_SCHEMAS["runtime_shadow_trace_manifest"],
            code="V1-E-RUNTIME-COVERAGE",
            artifact_path=manifest_rel,
        )
    trace_raw = source.files.get(trace_rel)
    if trace_raw is None:
        raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "runtime shadow trace is missing", artifact_path=trace_rel)
    if trace_manifest["event_jsonl_sha256"] != _sha256(trace_raw):
        raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow trace hash differs from manifest", artifact_path=trace_rel)
    events = list(strict_iter_jsonl(io.BytesIO(trace_raw), max(len(trace_raw), 1)))
    if trace_manifest["event_count"] != len(events):
        raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow trace event count differs from manifest", artifact_path=trace_rel)
    for event in events:
        _validate_schema(
            event,
            _V3_SCHEMAS["runtime_shadow_trace_event"],
            code="V1-E-RUNTIME-COVERAGE",
            artifact_path=trace_rel,
        )
        if event["run_id"] != source.run_id or event["source_commit"] != source.manifest["implementation_commit"]:
            raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow event run or source commit differs", artifact_path=trace_rel)
        if event["legacy_result_sha256"] != event["candidate_result_sha256"] or event["semantic_parity"] is not True:
            raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow event lacks hash and semantic parity", artifact_path=trace_rel)
        if event["write_attempted"] != bool(event["write_paths"]):
            raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow write-attempt flag and paths disagree", artifact_path=trace_rel)
        resolved = event["resolved_registry_paths"]
        if resolved["legacy_repository_path"] != _SOURCE_REGISTRY_PATH:
            raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow event resolved the wrong legacy path", artifact_path=trace_rel)
        _validate_artifact_relpath(resolved["candidate_prototype_path"])
        for item in event["write_paths"]:
            if item["path_context"] == "REPOSITORY_RELPATH":
                _validate_repository_relpath(item["path"])
            else:
                _validate_artifact_relpath(item["path"])
    if trace_manifest["run_id"] != source.run_id:
        raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow manifest run differs from candidate", artifact_path=manifest_rel)
    expected_required = sum(row["runtime_trace_required"] for row in consumers)
    if trace_manifest["required_consumer_count"] != expected_required:
        raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow required-consumer count differs from source map", artifact_path=manifest_rel)
    if (
        trace_manifest["required_consumers_observed"] != expected_required
        or trace_manifest["unobserved_required_consumer_count"] != 0
        or trace_manifest["unclassified_consumer_count"] != 0
        or trace_manifest["semantic_mismatch_count"] != 0
        or trace_manifest["operation_class_coverage_complete"] is not True
        or trace_manifest["migration_batch_coverage_complete"] is not True
        or trace_manifest["consumer_migration_performed"] is not False
        or trace_manifest["cutover_performed"] is not False
    ):
        raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "shadow manifest does not establish complete non-cutover parity", artifact_path=manifest_rel)
    observed_ids = {event["consumer_id"] for event in events}
    required_ids = {row["consumer_id"] for row in consumers if row["runtime_trace_required"]}
    if not required_ids.issubset(observed_ids):
        raise RegistryValidationError("V1-E-RUNTIME-COVERAGE", "not every required consumer was observed", artifact_path=trace_rel)
    return consumer_map, trace_manifest


def _validate_writer_probe(source: ArtifactSource, probe: Mapping[str, Any]) -> None:
    rel = "validation/LOOP_CONTROL_WRITER_PROBE_v1.json"
    _validate_schema(probe, _RUNTIME_SCHEMAS["writer_probe"], code="V1-E-WRITE-SCOPE", artifact_path=rel)
    if probe["run_id"] != source.run_id:
        raise RegistryValidationError("V1-E-WRITE-SCOPE", "writer probe run differs from candidate", artifact_path=rel)
    if probe["writes_outside_run_root"] != 0 or probe["history_mutation_performed"] or probe["new_api_write_performed"]:
        raise RegistryValidationError("V1-E-WRITE-SCOPE", "writer probe observed a prohibited write", artifact_path=rel)
    if probe["source_registry_sha256_before"] != SOURCE_REGISTRY_SHA256 or probe["source_registry_sha256_after"] != SOURCE_REGISTRY_SHA256:
        raise RegistryValidationError("V1-E-WRITE-SCOPE", "legacy registry hash changed during writer probe", artifact_path=rel)
    for attempted in probe["attempted_writes"]:
        if attempted["path_context"] != "PROTOTYPE_ARTIFACT_RELPATH":
            raise RegistryValidationError("V1-E-WRITE-SCOPE", "writer probe attempted a repository path write", artifact_path=rel)
        _validate_artifact_relpath(attempted["path"])
        if attempted["path"].startswith("history/shards/"):
            raise RegistryValidationError("V1-E-CLOSED-SHARD-WRITE", "writer probe attempted to modify a closed history shard", artifact_path=rel)


def _validate_prototype_integrity_source(source: ArtifactSource, anchors: ReviewedTrustAnchors) -> dict[str, Any]:
    anchors = _coerce_mapping(anchors, "anchors")
    anchor_hash = _trust_anchor_sha256(anchors)
    anchor_rel = "authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json"
    if source.files.get(anchor_rel) != canonical_artifact_bytes(anchors):
        raise RegistryValidationError("V1-E-AUTHORITY-EXTERNAL-BINDING", "candidate anchor artifact differs from external reviewed anchors", artifact_path=anchor_rel)
    if any(path in source.files for path in (
        "validation/LOOP_CONTROL_CONTROL_HARNESS_REPORT_v1.json",
        "validation/LOOP_CONTROL_STAGE_B_FULL_HARNESS_RESULT_v1.json",
    )):
        raise RegistryValidationError("V1-E-READINESS-PROFILE-CLOSURE", "Stage-A candidate contains a Stage-B/final-harness artifact")
    projection = _validate_projection(source, anchors)
    index, records = _validate_history(source, anchors, projection)
    custody = _validate_custody(source, anchors, records)
    consumer_rel = "consumers/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2.json"
    custody_rel = "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1.json"
    for pointer, rel in ((index["consumer_source_map_pointer"], consumer_rel), (index["custody_manifest_pointer"], custody_rel)):
        if pointer["path"] != rel or pointer["sha256"] != _sha256(source.files[rel]):
            raise RegistryValidationError("V1-E-INDEX-POINTER", f"history pointer does not bind {rel}", artifact_path="history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json")
    # The static map is structurally checked here; runtime completion belongs to
    # SHADOW_PARITY so PROTOTYPE_INTEGRITY remains compositional.
    _load_source_json(source, consumer_rel, "consumer_source_map")
    return {
        "candidate_tree_sha256": source.candidate_tree_sha256,
        "trust_anchor_sha256": anchor_hash,
        "projection": projection,
        "history_index": index,
        "record_count": len(records),
        "custody_manifest": custody,
    }


def _validate_write_safety_source(
    source: ArtifactSource,
    anchors: ReviewedTrustAnchors,
    writer_probe: WriterProbe,
) -> dict[str, Any]:
    base = _validate_prototype_integrity_source(source, anchors)
    _validate_writer_probe(source, _coerce_mapping(writer_probe, "writer_probe"))
    return base


def _validate_shadow_parity_source(
    source: ArtifactSource,
    anchors: ReviewedTrustAnchors,
    runtime_trace_manifest: ShadowTraceManifest,
) -> dict[str, Any]:
    # WRITE_SAFETY is part of the ordered prefix.  The externally supplied probe
    # is validated by validate_stage_a_candidate before this internal adapter.
    base = _validate_prototype_integrity_source(source, anchors)
    _validate_consumer_and_trace(source, _coerce_mapping(runtime_trace_manifest, "runtime_trace_manifest"))
    return base


def _validate_cutover_eligibility_source(
    source: ArtifactSource,
    anchors: ReviewedTrustAnchors,
    accepted_stage_a: ReviewedStageAAcceptance,
) -> dict[str, Any]:
    del source, anchors, accepted_stage_a
    raise RegistryValidationError("V1-E-STAGE-B-NOT-AUTHORIZED", "cutover eligibility is unavailable in Stage A")


def _profile_metadata(profile: str) -> Mapping[str, Any]:
    return _V3_PROTOCOL["validator_profile_composition"]["named_entrypoints"][profile]


def _issue_sort_key(issue: Mapping[str, Any]) -> tuple[str, str, str, str, str]:
    return (
        str(issue.get("error_code", "")),
        str(issue.get("artifact_path", "")),
        str(issue.get("json_pointer", "")),
        str(issue.get("message", "")),
        str(issue.get("control_id") or ""),
    )


def _profile_report(
    profile: str,
    candidate_root: Path,
    anchors: Mapping[str, Any],
    operation: Any,
) -> dict[str, Any]:
    candidate_hash = "0" * 64
    anchor_hash = "0" * 64
    issues: list[dict[str, Any]] = []
    try:
        anchor_hash = _trust_anchor_sha256(_coerce_mapping(anchors, "anchors"))
        source = resolve_artifact_source(Path(candidate_root))
        candidate_hash = source.candidate_tree_sha256
        operation(source)
    except RegistryValidationError as exc:
        issues.append(exc.issue())
    metadata = _profile_metadata(profile)
    issues = sorted({json.dumps(x, sort_keys=True): x for x in issues}.values(), key=_issue_sort_key)
    passed = not issues
    report = {
        "candidate_root_sha256": candidate_hash,
        "effective_control_count": metadata["effective_control_count"],
        "executed_profile_closure": list(metadata["ordered_closure"]),
        "profile": profile,
        "profile_control_root_sha256": metadata["effective_control_root_sha256"],
        "schema_id": "LOOP_CONTROL_VALIDATION_REPORT_READINESS_v3",
        "trust_anchor_sha256": anchor_hash,
        "issues": issues,
        "passed": passed,
        "status": "PASSED" if passed else "FAILED",
    }
    # Contract-level validation is itself fail closed, but do not mask the
    # primary typed issue with a secondary report-format issue.
    try:
        _validate_schema(report, _V3_SCHEMAS["validation_report"], code="V1-E-VALIDATION-REPORT-INVARIANT", artifact_path="validation/LOOP_CONTROL_REGISTRY_V1_VALIDATION_REPORT.json")
    except RegistryValidationError:
        if passed:
            raise
    return report


def validate_prototype_integrity(candidate_root: Path, anchors: ReviewedTrustAnchors) -> dict[str, Any]:
    return _profile_report(
        "PROTOTYPE_INTEGRITY",
        candidate_root,
        _coerce_mapping(anchors, "anchors"),
        lambda source: _validate_prototype_integrity_source(source, anchors),
    )


def validate_write_safety(candidate_root: Path, anchors: ReviewedTrustAnchors, writer_probe: WriterProbe) -> dict[str, Any]:
    return _profile_report(
        "WRITE_SAFETY",
        candidate_root,
        _coerce_mapping(anchors, "anchors"),
        lambda source: _validate_write_safety_source(source, anchors, writer_probe),
    )


def validate_shadow_parity(
    candidate_root: Path,
    anchors: ReviewedTrustAnchors,
    runtime_trace_manifest: ShadowTraceManifest,
) -> dict[str, Any]:
    return _profile_report(
        "SHADOW_PARITY",
        candidate_root,
        _coerce_mapping(anchors, "anchors"),
        lambda source: _validate_shadow_parity_source(source, anchors, runtime_trace_manifest),
    )


def validate_cutover_eligibility(
    candidate_root: Path,
    anchors: ReviewedTrustAnchors,
    accepted_stage_a: ReviewedStageAAcceptance,
) -> dict[str, Any]:
    del candidate_root, anchors, accepted_stage_a
    raise RegistryValidationError(
        "V1-E-STAGE-B-NOT-AUTHORIZED",
        "Stage B and cutover eligibility are not authorized by this contract",
    )


def require_valid(report: Mapping[str, Any]) -> None:
    if report.get("passed") is not True or report.get("status") != "PASSED" or report.get("issues"):
        issues = report.get("issues") or []
        if issues:
            first = issues[0]
            raise RegistryValidationError(
                first.get("error_code", "V1-E-NONCONTROL-DIAGNOSTIC"),
                first.get("message", "validation failed"),
                artifact_path=first.get("artifact_path", "validation/LOOP_CONTROL_REGISTRY_V1_VALIDATION_REPORT.json"),
                json_pointer=first.get("json_pointer", ""),
                control_id=first.get("control_id"),
            )
        raise RegistryValidationError("V1-E-NONCONTROL-DIAGNOSTIC", "validation report did not pass")


def validate_validation_report_contract(
    report: Mapping[str, Any],
    expected_profile: str,
    expected_candidate_root_sha256: str,
    expected_trust_anchor_sha256: str,
) -> Mapping[str, Any]:
    _validate_schema(report, _V3_SCHEMAS["validation_report"], code="V1-E-VALIDATION-REPORT-INVARIANT", artifact_path="validation/report.json")
    metadata = _profile_metadata(expected_profile)
    if (
        report["profile"] != expected_profile
        or report["candidate_root_sha256"] != expected_candidate_root_sha256
        or report["trust_anchor_sha256"] != expected_trust_anchor_sha256
        or report["executed_profile_closure"] != metadata["ordered_closure"]
        or report["effective_control_count"] != metadata["effective_control_count"]
        or report["profile_control_root_sha256"] != metadata["effective_control_root_sha256"]
        or report["passed"] != (report["status"] == "PASSED" and not report["issues"])
        or report["issues"] != sorted(report["issues"], key=_issue_sort_key)
    ):
        raise RegistryValidationError("V1-E-VALIDATION-REPORT-INVARIANT", "validation report invariants failed")
    return report


def validate_control_harness_report_contract(
    report: Mapping[str, Any],
    expected_base_candidate_sha256: str,
    expected_profile_control_roots: Mapping[str, str],
) -> Mapping[str, Any]:
    _validate_schema(report, _V3_SCHEMAS["control_harness_report"], code="V1-E-HARNESS-REPORT-INVARIANT", artifact_path="validation/harness.json")
    if report["base_candidate_sha256_before"] != expected_base_candidate_sha256 or report["base_candidate_sha256_after"] != expected_base_candidate_sha256:
        raise RegistryValidationError("V1-E-HARNESS-REPORT-INVARIANT", "harness baseline changed")
    if report["status"] != "ALL_CONTROLS_PASSED" or report["migration_controls_passed"] != 52 or report["readiness_regressions_passed"] != 8:
        raise RegistryValidationError("V1-E-HARNESS-REPORT-INVARIANT", "full harness success invariants failed")
    for profile, root in expected_profile_control_roots.items():
        if report["profile_reports"][profile]["effective_control_root_sha256"] != root:
            raise RegistryValidationError("V1-E-HARNESS-REPORT-INVARIANT", "harness profile root differs")
    return report


def _runtime_contract_result(code: str, action: Any) -> RuntimeContractReport:
    try:
        action()
    except RegistryValidationError as exc:
        issue = exc.issue()
        issue["error_code"] = code
        return RuntimeContractReport(False, code, (issue,))
    return RuntimeContractReport(True, None, ())


def _context_mapping(context: Any) -> Mapping[str, Any]:
    if context is None:
        return {}
    return _coerce_mapping(context, "runtime validation context")


def validate_reviewed_trust_anchors_contract(payload: object, review_context: Any) -> RuntimeContractReport:
    def check() -> None:
        anchors = _coerce_mapping(payload, "reviewed trust anchors")
        _validate_schema(anchors, _RUNTIME_SCHEMAS["reviewed_trust_anchors"], code="V1-E-RUNTIME-SCHEMA", artifact_path="authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json")
        context = _context_mapping(review_context)
        expected_sha = context.get("independent_review_sha256") or context.get("expected_sha256")
        if expected_sha is not None and anchors["prototype_execution_authorization"]["independent_review_sha256"] != expected_sha:
            raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "trust anchors differ from Git review context")
        review_commit = context.get("authorization_review_commit") or context.get("review_commit")
        if review_commit is not None and anchors["prototype_execution_authorization"]["authorization_review_commit"] != review_commit:
            raise RegistryValidationError("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", "trust-anchor review commit differs")
    return _runtime_contract_result("V1-E-TRUST-ANCHOR-EXTERNAL-BINDING", check)


def validate_artifact_source_manifest_contract(payload: object, candidate_root: Path) -> RuntimeContractReport:
    def check() -> None:
        manifest = _coerce_mapping(payload, "artifact source manifest")
        _validate_schema(manifest, _RUNTIME_SCHEMAS["artifact_source_manifest"], code="V1-E-RUNTIME-SCHEMA", artifact_path=_SOURCE_MANIFEST_REL)
        source = resolve_artifact_source(Path(candidate_root))
        if manifest != source.manifest:
            raise RegistryValidationError("V1-E-ARTIFACT-INVENTORY", "supplied artifact manifest differs from candidate")
    return _runtime_contract_result("V1-E-ARTIFACT-INVENTORY", check)


def validate_writer_probe_contract(payload: object, observed_writes: Any) -> RuntimeContractReport:
    def check() -> None:
        probe = _coerce_mapping(payload, "writer probe")
        _validate_schema(probe, _RUNTIME_SCHEMAS["writer_probe"], code="V1-E-RUNTIME-SCHEMA", artifact_path="validation/LOOP_CONTROL_WRITER_PROBE_v1.json")
        observation = _context_mapping(observed_writes)
        outside = observation.get("writes_outside_run_root", 0)
        history = observation.get("history_mutation_performed", False)
        api_write = observation.get("new_api_write_performed", False)
        if outside != 0 or history or api_write:
            raise RegistryValidationError("V1-E-WRITER-PROBE", "observed writes violate read-only scope")
        if probe["writes_outside_run_root"] != outside or probe["history_mutation_performed"] != history or probe["new_api_write_performed"] != api_write:
            raise RegistryValidationError("V1-E-WRITER-PROBE", "writer probe differs from observation")
    return _runtime_contract_result("V1-E-WRITER-PROBE", check)


def validate_run_rollback_inventory_contract(payload: object, filesystem_delta: Any) -> RuntimeContractReport:
    def check() -> None:
        inventory = _coerce_mapping(payload, "rollback inventory")
        _validate_schema(inventory, _RUNTIME_SCHEMAS["run_rollback_inventory"], code="V1-E-RUNTIME-SCHEMA", artifact_path="manifests/LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v1.json")
        created = inventory["created_paths"]
        if created != sorted(created, key=lambda x: x.encode("utf-8")) or len(set(created)) != len(created):
            raise RegistryValidationError("V1-E-ROLLBACK-INVENTORY", "rollback paths are not unique and sorted")
        expected_root = _plain_root(created)
        if inventory["created_paths_root_sha256"] != expected_root or inventory["outside_run_root_created_path_count"] != 0:
            raise RegistryValidationError("V1-E-ROLLBACK-INVENTORY", "rollback inventory root or scope differs")
        delta = _context_mapping(filesystem_delta)
        observed = delta.get("created_paths")
        if observed is not None and list(observed) != created:
            raise RegistryValidationError("V1-E-ROLLBACK-INVENTORY", "rollback inventory differs from filesystem delta")
    return _runtime_contract_result("V1-E-ROLLBACK-INVENTORY", check)


def validate_typed_result_envelope_contract(payload: object) -> RuntimeContractReport:
    def check() -> None:
        envelope = _coerce_mapping(payload, "typed result envelope")
        _validate_schema(envelope, _RUNTIME_SCHEMAS["typed_result_envelope"], code="V1-E-RUNTIME-SCHEMA", artifact_path="traces/LOOP_CONTROL_RUNTIME_SHADOW_TRACE_v1.jsonl")
        field = "canonical_json_utf8_base64" if envelope["result_kind"] == "VALUE" else "message_utf8_base64"
        try:
            decoded = base64.b64decode(envelope[field], validate=True)
        except (binascii.Error, ValueError) as exc:
            raise RegistryValidationError("V1-E-RESULT-ENVELOPE", "typed result payload is not strict base64") from exc
        if base64.b64encode(decoded).decode("ascii") != envelope[field] or _sha256(decoded) != envelope["payload_sha256"]:
            raise RegistryValidationError("V1-E-RESULT-ENVELOPE", "typed result payload identity differs")
        if envelope["result_kind"] == "VALUE":
            parsed = strict_load_json(decoded, "TYPED_RESULT_VALUE")
            if _canonical_compact(parsed) != decoded:
                raise RegistryValidationError("V1-E-RESULT-ENVELOPE", "typed result value is not canonical JSON")
        else:
            try:
                decoded.decode("utf-8", errors="strict")
            except UnicodeDecodeError as exc:
                raise RegistryValidationError("V1-E-RESULT-ENVELOPE", "typed exception message is not UTF-8") from exc
    return _runtime_contract_result("V1-E-RESULT-ENVELOPE", check)


def _result_rows_root(domain: str, rows: Sequence[Mapping[str, Any]]) -> str:
    return _canonical_domain_root(domain, (_canonical_compact(row) for row in rows))


def validate_stage_a_precutover_report_contract(payload: object, expected_controls: Any) -> RuntimeContractReport:
    def check() -> None:
        report = _coerce_mapping(payload, "Stage-A report")
        _validate_schema(report, _RUNTIME_SCHEMAS["stage_a_precutover_report"], code="V1-E-RUNTIME-SCHEMA", artifact_path="validation/LOOP_CONTROL_STAGE_A_PRECUTOVER_REPORT_v1.json")
        expected = _context_mapping(expected_controls)
        if [row["control_id"] for row in report["control_results"]] != list(STAGE_A_CONTROL_IDS):
            raise RegistryValidationError("V1-E-STAGE-A-CONTROL-RESULT", "Stage-A inherited controls are missing or reordered")
        if [row["control_id"] for row in report["runtime_contract_control_results"]] != list(STAGE_A_RUNTIME_IDS):
            raise RegistryValidationError("V1-E-STAGE-A-CONTROL-RESULT", "Stage-A runtime controls are missing or reordered")
        if not all(row["passed"] for row in report["control_results"] + report["runtime_contract_control_results"]):
            raise RegistryValidationError("V1-E-STAGE-A-CONTROL-RESULT", "Stage-A report contains a failed control")
        root = _result_rows_root("LOOP_CONTROL_STAGE_A_CONTROL_RESULTS_ROOT_v1", report["control_results"])
        runtime_root = _result_rows_root("LOOP_CONTROL_STAGE_A_RUNTIME_CONTRACT_RESULTS_ROOT_v1", report["runtime_contract_control_results"])
        if report["control_results_root_sha256"] != root or report["runtime_contract_results_root_sha256"] != runtime_root:
            raise RegistryValidationError("V1-E-STAGE-A-CONTROL-RESULT", "Stage-A control result root differs")
        candidate = expected.get("candidate_tree_sha256")
        if candidate is not None and report["candidate_tree_sha256"] != candidate:
            raise RegistryValidationError("V1-E-STAGE-A-BASELINE", "Stage-A candidate binding differs")
        if report["cutover_controls_executed"] != 0 or report["final_harness_report_emitted"]:
            raise RegistryValidationError("V1-E-STAGE-A-CONTROL-RESULT", "Stage-A report claims cutover/full harness execution")
    return _runtime_contract_result("V1-E-STAGE-A-CONTROL-RESULT", check)


def validate_stage_a_acceptance_binding_contract(payload: object, review_context: Any) -> RuntimeContractReport:
    def check() -> None:
        binding = _coerce_mapping(payload, "Stage-A acceptance")
        _validate_schema(binding, _RUNTIME_SCHEMAS["stage_a_acceptance_binding"], code="V1-E-RUNTIME-SCHEMA", artifact_path="formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_STAGE_A_INDEPENDENT_REVIEW_20260711_v0.json")
        context = _context_mapping(review_context)
        if context.get("source") != "INDEPENDENT_STAGE_A_REVIEW_IN_GIT" or not binding["accepted"]:
            raise RegistryValidationError("V1-E-STAGE-A-ACCEPTANCE", "Stage-A acceptance is not externally Git reviewed")
    return _runtime_contract_result("V1-E-STAGE-A-ACCEPTANCE", check)


def validate_stage_b_full_harness_result_contract(payload: object, accepted_stage_a: ReviewedStageAAcceptance) -> RuntimeContractReport:
    del payload, accepted_stage_a
    return RuntimeContractReport(
        False,
        "V1-E-STAGE-B-NOT-AUTHORIZED",
        ({"error_code": "V1-E-STAGE-B-NOT-AUTHORIZED", "message": "Stage B is unauthorized", "artifact_path": "validation/LOOP_CONTROL_STAGE_B_FULL_HARNESS_RESULT_v1.json", "json_pointer": "", "control_id": None},),
    )


def _parse_utc(value: str) -> datetime:
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.tzinfo is None or parsed.utcoffset() != timezone.utc.utcoffset(parsed):
        raise ValueError("not UTC")
    return parsed


def validate_runtime_run_manifest_contract(payload: object, observed_run: Any) -> RuntimeContractReport:
    def check() -> None:
        manifest = _coerce_mapping(payload, "runtime run manifest")
        _validate_schema(manifest, _RUNTIME_SCHEMAS["runtime_run_manifest"], code="V1-E-RUNTIME-SCHEMA", artifact_path="manifests/LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v1.json")
        try:
            started, finished = _parse_utc(manifest["started_at_utc"]), _parse_utc(manifest["finished_at_utc"])
        except (ValueError, TypeError) as exc:
            raise RegistryValidationError("V1-E-RUNTIME-FORMAT", "runtime timestamps are not canonical UTC date-times") from exc
        if started > finished or manifest["stage"] != "STAGE_A" or manifest["timed_out"]:
            raise RegistryValidationError("V1-E-RUN-MANIFEST", "runtime run manifest is not a completed Stage-A run")
        observed = _context_mapping(observed_run)
        if observed.get("run_id", manifest["run_id"]) != manifest["run_id"]:
            raise RegistryValidationError("V1-E-RUN-MANIFEST", "runtime manifest differs from observed run")
    return _runtime_contract_result("V1-E-RUN-MANIFEST", check)


def _consumer_delta_root(rows: Sequence[Mapping[str, Any]]) -> str:
    ordered = sorted(rows, key=lambda row: row["path"].encode("utf-8"))
    return _canonical_domain_root("LOOP_CONTROL_CONSUMER_INVENTORY_DELTA_ROOT_v1", (_canonical_compact(row) for row in ordered))


def validate_execution_preflight_contract(payload: object, git_context: Any) -> RuntimeContractReport:
    def check() -> None:
        preflight = _coerce_mapping(payload, "execution preflight")
        _validate_schema(preflight, _RUNTIME_SCHEMAS["execution_preflight"], code="V1-E-RUNTIME-SCHEMA", artifact_path="manifests/LOOP_CONTROL_EXECUTION_PREFLIGHT_v1.json")
        context = _context_mapping(git_context)
        if preflight["consumer_inventory_delta_root_sha256"] != _consumer_delta_root(preflight["consumer_inventory_rows"]):
            raise RegistryValidationError("V1-E-CONSUMER-INVENTORY-DELTA", "consumer inventory delta root differs")
        nonretired = sum(row["delta_class"] != "RETIRED" for row in preflight["consumer_inventory_rows"])
        if preflight["current_consumer_path_count"] != nonretired or len({row["path"] for row in preflight["consumer_inventory_rows"]}) != len(preflight["consumer_inventory_rows"]):
            raise RegistryValidationError("V1-E-CONSUMER-INVENTORY-DELTA", "consumer inventory count or paths differ")
        if not _git_is_ancestor(preflight["authorization_review_commit"], preflight["implementation_commit"]):
            raise RegistryValidationError("V1-E-PREFLIGHT-GIT-BINDING", "authorization review is not an implementation ancestor")
        for key in ("implementation_commit", "head_commit", "main_commit", "origin_main_commit"):
            expected = context.get(key)
            if expected is not None and preflight[key] != expected:
                raise RegistryValidationError("V1-E-PREFLIGHT-GIT-BINDING", f"preflight {key} differs from Git context")
    return _runtime_contract_result("V1-E-PREFLIGHT-GIT-BINDING", check)


def validate_runtime_cross_document_invariants(artifacts: Any, candidate_root: Path) -> RuntimeContractReport:
    def check() -> None:
        docs = _context_mapping(artifacts)
        run_ids = {
            value["run_id"]
            for value in docs.values()
            if isinstance(value, Mapping) and isinstance(value.get("run_id"), str)
        }
        if len(run_ids) > 1:
            raise RegistryValidationError("V1-E-RUNTIME-CROSS-DOCUMENT", "runtime documents have inconsistent run IDs")
        source = resolve_artifact_source(Path(candidate_root))
        if run_ids and source.run_id not in run_ids:
            raise RegistryValidationError("V1-E-RUNTIME-CROSS-DOCUMENT", "runtime documents differ from candidate run ID")
        # If both documents exist, enforce the mutually required hash pointer.
        run_manifest = docs.get("runtime_run_manifest")
        source_manifest = docs.get("artifact_source_manifest")
        if isinstance(run_manifest, Mapping) and isinstance(source_manifest, Mapping):
            actual = canonical_artifact_bytes(source_manifest)
            pointer = run_manifest["artifact_source_manifest"]
            if pointer["sha256"] != _sha256(actual) or pointer["size_bytes"] != len(actual):
                raise RegistryValidationError("V1-E-RUNTIME-CROSS-DOCUMENT", "run manifest does not bind artifact source manifest")
    return _runtime_contract_result("V1-E-RUNTIME-CROSS-DOCUMENT", check)


STAGE_A_CONTRACT_CYCLE_ERROR = "V1-E-UNSATISFIABLE-ARTIFACT-MANIFEST-CYCLE"


def stage_a_contract_cycle_diagnostic() -> Mapping[str, Any]:
    """Return the reviewed-contract dependency cycle that blocks execution."""

    artifact_contract = _EXECUTION_CONTRACT["artifact_source_and_candidate_tree_contract"]
    run_schema = _RUNTIME_SCHEMAS["runtime_run_manifest"]
    mapping = _EXECUTION_CONTRACT["runtime_schema_artifact_mapping"]
    source_is_standalone = mapping["artifact_source_manifest"]["disposition"] == "STANDALONE"
    run_is_standalone = mapping["runtime_run_manifest"]["disposition"] == "STANDALONE"
    run_binds_source_sha = "artifact_source_manifest" in run_schema["required"] and "sha256" in run_schema["properties"]["artifact_source_manifest"]["required"]
    source_inventories_run = artifact_contract["all_other_regular_run_root_artifacts_are_inventoried_exactly_once"] is True
    cycle = source_is_standalone and run_is_standalone and run_binds_source_sha and source_inventories_run
    return {
        "error_code": STAGE_A_CONTRACT_CYCLE_ERROR if cycle else None,
        "cycle_present": cycle,
        "artifact_source_manifest_depends_on": "SHA256(runtime_run_manifest_bytes)",
        "runtime_run_manifest_depends_on": "SHA256(artifact_source_manifest_bytes)",
        "accepted_contract_supplies_cycle_break_rule": False,
        "stage_a_execution_satisfiable": not cycle,
    }


def assert_stage_a_contract_satisfiable() -> None:
    diagnostic = stage_a_contract_cycle_diagnostic()
    if diagnostic["cycle_present"]:
        raise RegistryValidationError(
            STAGE_A_CONTRACT_CYCLE_ERROR,
            "accepted Stage-A contract requires reciprocal artifact-source/run-manifest SHA-256 bindings without a staged exclusion or terminal-envelope rule",
            artifact_path=_SOURCE_MANIFEST_REL,
        )


def validate_stage_a_candidate(
    candidate_root: Path,
    anchors: Mapping[str, Any],
    writer_probe: Mapping[str, Any],
    trace_manifest: Mapping[str, Any],
) -> dict[str, Any]:
    """Validate Stage A only; currently fails before evidence due to contract cycle."""

    assert_stage_a_contract_satisfiable()
    reports = {
        "PROTOTYPE_INTEGRITY": validate_prototype_integrity(candidate_root, anchors),
        "WRITE_SAFETY": validate_write_safety(candidate_root, anchors, writer_probe),
        "SHADOW_PARITY": validate_shadow_parity(candidate_root, anchors, trace_manifest),
    }
    passed = all(report["passed"] for report in reports.values())
    return {"passed": passed, "reports": reports, "cutover_profile_executed": False, "stage_b_executed": False}


def run_stage_a_controls(
    candidate_root: Path,
    anchors: Mapping[str, Any],
    writer_probe: Mapping[str, Any],
    trace_manifest: Mapping[str, Any],
    runtime_artifacts: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Run exactly 58+18 controls, or fail before evidence if unsatisfiable.

    No result rows are synthesized on failure.  In particular, this function
    cannot emit apparently passing 76-control evidence for the reciprocal-hash
    contract cycle.
    """

    del candidate_root, anchors, writer_probe, trace_manifest, runtime_artifacts
    assert_stage_a_contract_satisfiable()
    raise AssertionError("unreachable until a reviewed successor resolves the Stage-A contract cycle")


def reconstruct_and_verify_legacy(candidate_root: Path, output: BinaryIO, anchors: ReviewedTrustAnchors) -> Mapping[str, Any]:
    source = resolve_artifact_source(candidate_root)
    _trust_anchor_sha256(_coerce_mapping(anchors, "anchors"))
    payload = source.files["custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz"]
    decoded = _decompress_single_gzip(payload)
    if len(decoded) != SOURCE_REGISTRY_SIZE or _sha256(decoded) != SOURCE_REGISTRY_SHA256:
        raise RegistryValidationError("V1-E-CUSTODY-HASH", "legacy reconstruction differs from frozen source")
    output.write(decoded)
    return {"sha256": _sha256(decoded), "size_bytes": len(decoded), "byte_identical": True}


__all__ = [
    "AmbiguousRegistryRecordIdError",
    "ArtifactSource",
    "RegistryRecordNotFoundError",
    "RegistryValidationError",
    "RuntimeContractReport",
    "STAGE_A_CONTRACT_CYCLE_ERROR",
    "STAGE_A_CONTROL_IDS",
    "STAGE_A_EXCLUDED_IDS",
    "STAGE_A_PRIMARY_IDS",
    "STAGE_A_READINESS_IDS",
    "STAGE_A_RUNTIME_IDS",
    "assert_stage_a_contract_satisfiable",
    "canonical_artifact_bytes",
    "load_reviewed_stage_a_acceptance",
    "load_reviewed_trust_anchors",
    "reconstruct_and_verify_legacy",
    "require_valid",
    "resolve_artifact_source",
    "run_stage_a_controls",
    "stage_a_contract_cycle_diagnostic",
    "strict_iter_jsonl",
    "strict_load_json",
    "validate_artifact_source_manifest_contract",
    "validate_control_harness_report_contract",
    "validate_cutover_eligibility",
    "validate_execution_preflight_contract",
    "validate_history_record_payload_contract",
    "validate_prototype_integrity",
    "validate_reviewed_trust_anchors_contract",
    "validate_run_rollback_inventory_contract",
    "validate_runtime_cross_document_invariants",
    "validate_runtime_run_manifest_contract",
    "validate_shadow_parity",
    "validate_stage_a_acceptance_binding_contract",
    "validate_stage_a_candidate",
    "validate_stage_a_precutover_report_contract",
    "validate_stage_b_full_harness_result_contract",
    "validate_typed_result_envelope_contract",
    "validate_validation_report_contract",
    "validate_write_safety",
    "validate_writer_probe_contract",
]
