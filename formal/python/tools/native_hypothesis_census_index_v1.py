from __future__ import annotations

"""Passive, deterministic custody-index infrastructure for the future census.

This module is maintenance infrastructure only.  Its command-line interface
refuses the repository's declared scientific archive roots and accepts only a
synthetic or explicitly nonauthoritative trial root.  A future Stage-1
producer must supply its own authority gate before using these primitives on
the installed program's source envelope.
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import hashlib
import json
import os
import re
import sqlite3
import stat
import subprocess
import time
import tracemalloc
import unicodedata
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.bounded_program_governance import (
    CENSUS_PROGRAM_ID,
    jcs_bytes,
)


REPO_ROOT = find_repo_root(Path(__file__))
INDEX_ID = "TOE_NATIVE_HYPOTHESIS_CENSUS_INDEX_V1"
INDEX_SCHEMA_VERSION = 1
HASHING_SCHEMA_VERSION = 1
PARSER_CONTRACT_VERSION = "v1"
DEFAULT_CACHE_PATH = (
    REPO_ROOT / ".toe_cache" / "native_hypothesis_census_v1.sqlite3"
)
LEGACY_INDEX_PATH = REPO_ROOT / "formal" / "output" / "archive_intake_index.json"
PROTECTED_SCIENTIFIC_ROOTS = (
    REPO_ROOT / "archive",
    REPO_ROOT / "archive" / "ToE_Project",
    REPO_ROOT / "archive" / "ToE_Project_Starter_2025-09-24",
)
CHUNK_BYTES = 1024 * 1024


@dataclass(frozen=True)
class ParserSpec:
    parser_id: str
    extensions: tuple[str, ...]
    max_file_bytes: int
    max_extracted_text_bytes: int
    timeout_seconds: int
    memory_limit_bytes: int
    maximum_nesting_or_recursion_depth: int | None = None
    maximum_record_or_cell_count: int | None = None
    maximum_page_or_worksheet_count: int | None = None


PARSER_SPECS = (
    ParserSpec(
        "PASSIVE_TEXT_SOURCE_V1",
        ("md", "txt", "py", "lean", "tex", "rst", "ps1", "sh", "cfg", "ini"),
        16 * 1024 * 1024,
        4 * 1024 * 1024,
        30,
        512 * 1024 * 1024,
        maximum_nesting_or_recursion_depth=32,
    ),
    ParserSpec(
        "PASSIVE_STRUCTURED_TEXT_V1",
        ("json", "yaml", "yml", "toml"),
        16 * 1024 * 1024,
        4 * 1024 * 1024,
        30,
        512 * 1024 * 1024,
        maximum_nesting_or_recursion_depth=64,
    ),
    ParserSpec(
        "PASSIVE_TABULAR_V1",
        ("csv", "tsv"),
        256 * 1024 * 1024,
        8 * 1024 * 1024,
        60,
        1024 * 1024 * 1024,
        maximum_record_or_cell_count=2_000_000,
    ),
    ParserSpec(
        "PASSIVE_PDF_V1",
        ("pdf",),
        128 * 1024 * 1024,
        8 * 1024 * 1024,
        120,
        1024 * 1024 * 1024,
        maximum_page_or_worksheet_count=1000,
    ),
    ParserSpec(
        "PASSIVE_OFFICE_V1",
        ("docx", "xlsx", "pptx", "odt", "ods", "odp"),
        128 * 1024 * 1024,
        8 * 1024 * 1024,
        120,
        1024 * 1024 * 1024,
        maximum_page_or_worksheet_count=1000,
    ),
    ParserSpec(
        "PASSIVE_NOTEBOOK_V1",
        ("ipynb",),
        64 * 1024 * 1024,
        8 * 1024 * 1024,
        60,
        1024 * 1024 * 1024,
        maximum_nesting_or_recursion_depth=64,
        maximum_record_or_cell_count=10_000,
    ),
    ParserSpec(
        "METADATA_ONLY_MEDIA_V1",
        ("png", "jpg", "jpeg", "gif", "svg", "wav", "mp3", "mp4"),
        1024 * 1024 * 1024,
        0,
        30,
        512 * 1024 * 1024,
    ),
    ParserSpec(
        "METADATA_ONLY_BINARY_DATA_V1",
        ("npy", "npz", "bin", "exe", "dll", "whl"),
        1024 * 1024 * 1024,
        0,
        30,
        512 * 1024 * 1024,
    ),
    ParserSpec(
        "CONTAINER_METADATA_ONLY_V1",
        ("zip", "tar", "gz", "7z", "rar"),
        1024 * 1024 * 1024,
        0,
        30,
        512 * 1024 * 1024,
        maximum_nesting_or_recursion_depth=0,
    ),
)
PARSER_BY_EXTENSION = {
    extension: spec for spec in PARSER_SPECS for extension in spec.extensions
}


class CensusIndexError(RuntimeError):
    pass


class UnsafePathError(CensusIndexError):
    pass


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalize_relative_path(value: str) -> str:
    if "\x00" in value:
        raise UnsafePathError("NUL is forbidden in custody paths")
    candidate = value.replace("\\", "/")
    if candidate.startswith("/") or re.match(r"^[A-Za-z]:", candidate):
        raise UnsafePathError("absolute custody path is forbidden")
    parts = PurePosixPath(candidate).parts
    if not parts or any(part in {"", ".", ".."} for part in parts):
        raise UnsafePathError("ambiguous or traversing custody path is forbidden")
    return PurePosixPath(*parts).as_posix()


def _inside(path: Path, root: Path) -> bool:
    try:
        path.resolve(strict=False).relative_to(root.resolve(strict=False))
    except ValueError:
        return False
    return True


def _is_reparse(stat_result: os.stat_result) -> bool:
    flag = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)
    return bool(getattr(stat_result, "st_file_attributes", 0) & flag)


def _file_extension(path: Path) -> str:
    return path.suffix.lower().lstrip(".")


def parser_spec_for(path: Path) -> ParserSpec | None:
    return PARSER_BY_EXTENSION.get(_file_extension(path))


def _sha256_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    bytes_read = 0
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(CHUNK_BYTES), b""):
            bytes_read += len(chunk)
            digest.update(chunk)
    return digest.hexdigest(), bytes_read


class HashCache:
    """SQLite cache whose local metadata keys are hints, never final evidence."""

    def __init__(self, path: Path):
        self.path = path
        self.connection: sqlite3.Connection | None = None

    def __enter__(self) -> "HashCache":
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.connection = sqlite3.connect(self.path)
        self.connection.execute("PRAGMA journal_mode=WAL")
        self.connection.execute("PRAGMA synchronous=FULL")
        self.connection.executescript(
            """
            CREATE TABLE IF NOT EXISTS git_blob_hash (
              object_format TEXT NOT NULL,
              object_id TEXT NOT NULL,
              schema_version INTEGER NOT NULL,
              sha256 TEXT NOT NULL,
              PRIMARY KEY (object_format, object_id, schema_version)
            );
            CREATE TABLE IF NOT EXISTS local_file_hash (
              source_root_id TEXT NOT NULL,
              relative_path TEXT NOT NULL,
              size INTEGER NOT NULL,
              mtime_ns INTEGER NOT NULL,
              schema_version INTEGER NOT NULL,
              sha256 TEXT NOT NULL,
              PRIMARY KEY (
                source_root_id, relative_path, size, mtime_ns, schema_version
              )
            );
            """
        )
        self.connection.commit()
        return self

    def __exit__(self, *_: object) -> None:
        if self.connection is not None:
            self.connection.commit()
            self.connection.close()
            self.connection = None

    def _db(self) -> sqlite3.Connection:
        if self.connection is None:
            raise CensusIndexError("hash cache is not open")
        return self.connection

    def get_git_blob(
        self, object_format: str, object_id: str
    ) -> str | None:
        row = self._db().execute(
            """
            SELECT sha256 FROM git_blob_hash
            WHERE object_format = ? AND object_id = ? AND schema_version = ?
            """,
            (object_format, object_id, HASHING_SCHEMA_VERSION),
        ).fetchone()
        return None if row is None else str(row[0])

    def put_git_blob(
        self, object_format: str, object_id: str, sha256: str
    ) -> None:
        with self._db():
            self._db().execute(
                """
                INSERT OR REPLACE INTO git_blob_hash
                (object_format, object_id, schema_version, sha256)
                VALUES (?, ?, ?, ?)
                """,
                (object_format, object_id, HASHING_SCHEMA_VERSION, sha256),
            )

    def get_local(
        self,
        source_root_id: str,
        relative_path: str,
        *,
        size: int,
        mtime_ns: int,
    ) -> str | None:
        row = self._db().execute(
            """
            SELECT sha256 FROM local_file_hash
            WHERE source_root_id = ? AND relative_path = ?
              AND size = ? AND mtime_ns = ? AND schema_version = ?
            """,
            (
                source_root_id,
                relative_path,
                size,
                mtime_ns,
                HASHING_SCHEMA_VERSION,
            ),
        ).fetchone()
        return None if row is None else str(row[0])

    def put_local(
        self,
        source_root_id: str,
        relative_path: str,
        *,
        size: int,
        mtime_ns: int,
        sha256: str,
    ) -> None:
        with self._db():
            self._db().execute(
                """
                INSERT OR REPLACE INTO local_file_hash
                (source_root_id, relative_path, size, mtime_ns,
                 schema_version, sha256)
                VALUES (?, ?, ?, ?, ?, ?)
                """,
                (
                    source_root_id,
                    relative_path,
                    size,
                    mtime_ns,
                    HASHING_SCHEMA_VERSION,
                    sha256,
                ),
            )


def git_blob_sha256(
    repo_root: Path, object_id: str, cache: HashCache
) -> tuple[str, bool]:
    object_format = subprocess.run(
        ["git", "rev-parse", "--show-object-format"],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    cached = cache.get_git_blob(object_format, object_id)
    if cached is not None:
        return cached, True
    blob = subprocess.run(
        ["git", "cat-file", "blob", object_id],
        cwd=repo_root,
        check=True,
        capture_output=True,
    ).stdout
    digest = sha256_bytes(blob)
    cache.put_git_blob(object_format, object_id, digest)
    return digest, False


def _bounded_read(path: Path, limit: int, deadline: float) -> tuple[bytes, bool]:
    output = bytearray()
    truncated = False
    with path.open("rb") as handle:
        while len(output) <= limit:
            if time.monotonic() > deadline:
                raise TimeoutError("passive extraction deadline exceeded")
            chunk = handle.read(min(CHUNK_BYTES, limit + 1 - len(output)))
            if not chunk:
                break
            output.extend(chunk)
        if len(output) > limit:
            del output[limit:]
            truncated = True
        elif handle.read(1):
            truncated = True
    return bytes(output), truncated


def _maximum_json_nesting(text: str) -> int:
    depth = 0
    maximum = 0
    in_string = False
    escape = False
    for char in text:
        if in_string:
            if escape:
                escape = False
            elif char == "\\":
                escape = True
            elif char == '"':
                in_string = False
            continue
        if char == '"':
            in_string = True
        elif char in "[{":
            depth += 1
            maximum = max(maximum, depth)
        elif char in "]}":
            depth = max(0, depth - 1)
    return maximum


def passive_extract(path: Path, spec: ParserSpec | None) -> dict[str, Any]:
    if spec is None:
        return {
            "parser_id": None,
            "content_extraction_status": "UNSUPPORTED_FORMAT_PRESERVED",
            "content_fingerprint": None,
            "extracted_text_bytes": 0,
        }
    size = path.stat().st_size
    if size > spec.max_file_bytes:
        return {
            "parser_id": spec.parser_id,
            "content_extraction_status": "FILE_SIZE_LIMIT_EXCEEDED",
            "content_fingerprint": None,
            "extracted_text_bytes": 0,
        }
    if spec.max_extracted_text_bytes == 0 or spec.parser_id in {
        "PASSIVE_PDF_V1",
        "PASSIVE_OFFICE_V1",
    }:
        return {
            "parser_id": spec.parser_id,
            "content_extraction_status": "METADATA_ONLY_NO_ACTIVE_CONTENT",
            "content_fingerprint": None,
            "extracted_text_bytes": 0,
        }
    deadline = time.monotonic() + spec.timeout_seconds
    try:
        data, truncated = _bounded_read(
            path, spec.max_extracted_text_bytes, deadline
        )
    except (OSError, TimeoutError):
        return {
            "parser_id": spec.parser_id,
            "content_extraction_status": "PARSER_FAILURE_PRESERVED",
            "content_fingerprint": None,
            "extracted_text_bytes": 0,
        }
    text = data.decode("utf-8", errors="replace")
    if (
        spec.maximum_nesting_or_recursion_depth is not None
        and _maximum_json_nesting(text)
        > spec.maximum_nesting_or_recursion_depth
    ):
        status = "NESTING_LIMIT_EXCEEDED"
    elif (
        spec.maximum_record_or_cell_count is not None
        and max(text.count("\n") + 1, text.count('"cell_type"'))
        > spec.maximum_record_or_cell_count
    ):
        status = "RECORD_OR_CELL_LIMIT_EXCEEDED"
    elif truncated:
        status = "EXTRACTED_TEXT_LIMIT_REACHED"
    else:
        status = "PASSIVE_TEXT_EXTRACTED"
    normalized = "\n".join(line.rstrip() for line in text.splitlines()).strip()
    return {
        "parser_id": spec.parser_id,
        "content_extraction_status": status,
        "content_fingerprint": sha256_bytes(normalized.encode("utf-8")),
        "extracted_text_bytes": len(data),
    }


def _iter_root_entries(root: Path) -> Iterable[tuple[Path, os.stat_result, str]]:
    if not root.is_dir():
        raise CensusIndexError(f"source root is not a directory: {root}")
    pending = [root]
    while pending:
        directory = pending.pop()
        try:
            entries = sorted(
                os.scandir(directory),
                key=lambda entry: os.fsencode(entry.name),
                reverse=True,
            )
        except OSError as error:
            raise CensusIndexError(f"cannot scan source root: {directory}") from error
        for entry in entries:
            path = Path(entry.path)
            info = entry.stat(follow_symlinks=False)
            if entry.is_symlink() or _is_reparse(info):
                yield path, info, "LINK_OR_REPARSE_POINT"
            elif entry.is_dir(follow_symlinks=False):
                pending.append(path)
            elif entry.is_file(follow_symlinks=False):
                yield path, info, "REGULAR_FILE"
            else:
                yield path, info, "SPECIAL_FILESYSTEM_OBJECT"


def _collision_key(relative_path: str) -> str:
    return unicodedata.normalize("NFC", relative_path).casefold()


def build_snapshot(
    *,
    source_root_id: str,
    root: Path,
    cache: HashCache,
    final_hash_verification: bool,
    extract_text: bool,
    worker_count: int = 1,
) -> dict[str, Any]:
    if worker_count != 1:
        raise CensusIndexError("maintenance v1 supports exactly one worker")
    started_wall = time.perf_counter()
    started_cpu = time.process_time()
    tracemalloc.start()
    records: list[dict[str, Any]] = []
    cache_reused = 0
    files_hashed = 0
    bytes_read = 0
    collisions: dict[str, list[str]] = {}

    for path, info, object_class in _iter_root_entries(root):
        try:
            relative_path = normalize_relative_path(
                path.relative_to(root).as_posix()
            )
        except (ValueError, UnsafePathError) as error:
            raise UnsafePathError(f"root-relative path rejected: {path}") from error
        if object_class == "REGULAR_FILE" and not _inside(path, root):
            raise UnsafePathError(f"file escaped source root: {relative_path}")
        collisions.setdefault(_collision_key(relative_path), []).append(relative_path)
        base_record: dict[str, Any] = {
            "source_root_id": source_root_id,
            "custody_relative_path": relative_path,
            "git_or_filesystem_status": "LOCAL_SYNTHETIC_MAINTENANCE_TRIAL",
            "git_object_id": None,
            "committed_blob_sha256": None,
            "worktree_sha256": None,
            "local_verified_sha256": None,
            "file_size": int(info.st_size),
            "date_metadata_with_kind_and_confidence": {
                "kind": "FILESYSTEM_MTIME_CACHE_HINT_ONLY",
                "mtime_ns": str(int(info.st_mtime_ns)),
                "confidence": "NOT_CONTENT_IDENTITY",
            },
            "file_type": (
                _file_extension(path) or "NO_EXTENSION"
                if object_class == "REGULAR_FILE"
                else object_class
            ),
            "content_fingerprint": None,
            "duplicate_group_candidate": None,
            "source_classification": "UNCLASSIFIED_MAINTENANCE_ONLY",
            "content_extraction_status": "NOT_ATTEMPTED",
            "domain_tags": [],
            "source_lineage": None,
            "provenance_status": "SYNTHETIC_OR_NONAUTHORITATIVE_TRIAL",
            "licensing_or_redistribution_concern": "NOT_ASSESSED",
            "custody_class": "LOCAL_REGENERABLE_NONAUTHORITATIVE",
            "eligibility_for_deeper_review": False,
            "exclusion_reason": "MAINTENANCE_TRIAL_NOT_SCIENTIFIC_EVIDENCE",
            "source_snapshot_id": None,
            "indexer_schema_version": INDEX_SCHEMA_VERSION,
            "parser_contract_version": PARSER_CONTRACT_VERSION,
            "filesystem_object_class": object_class,
        }
        if object_class != "REGULAR_FILE":
            base_record["content_extraction_status"] = (
                "SAFETY_BLOCKED_NO_FOLLOW"
            )
            records.append(base_record)
            continue
        cached = None
        if not final_hash_verification:
            cached = cache.get_local(
                source_root_id,
                relative_path,
                size=int(info.st_size),
                mtime_ns=int(info.st_mtime_ns),
            )
        if cached is None:
            digest, read_count = _sha256_file(path)
            files_hashed += 1
            bytes_read += read_count
            cache.put_local(
                source_root_id,
                relative_path,
                size=int(info.st_size),
                mtime_ns=int(info.st_mtime_ns),
                sha256=digest,
            )
        else:
            digest = cached
            cache_reused += 1
        base_record["local_verified_sha256"] = digest
        if extract_text:
            extraction = passive_extract(path, parser_spec_for(path))
            base_record.update(extraction)
        records.append(base_record)

    normalized_collisions = [
        sorted(paths)
        for paths in collisions.values()
        if len(set(paths)) > 1
    ]
    collision_members = {
        path for group in normalized_collisions for path in group
    }
    hashes: dict[str, list[str]] = {}
    for record in records:
        digest = record["local_verified_sha256"]
        if digest is not None:
            hashes.setdefault(digest, []).append(record["custody_relative_path"])
    for record in records:
        digest = record["local_verified_sha256"]
        if digest is not None and len(hashes[digest]) > 1:
            record["duplicate_group_candidate"] = (
                f"EXACT_CONTENT_DUPLICATE:{digest}"
            )
        if record["custody_relative_path"] in collision_members:
            record["content_extraction_status"] = (
                "FILENAME_NORMALIZATION_COLLISION_BLOCKED"
            )

    records.sort(
        key=lambda row: row["custody_relative_path"].encode("utf-8")
    )
    tuples = [
        {
            "normalized_relative_path": row["custody_relative_path"],
            "file_type": row["file_type"],
            "size": row["file_size"],
            "sha256": row["local_verified_sha256"],
            "custody_classification": row["custody_class"],
        }
        for row in records
    ]
    tuple_hash = sha256_bytes(jcs_bytes(tuples))
    for row in records:
        row["source_snapshot_id"] = tuple_hash
    _, peak_memory = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    return {
        "schema_id": "toe.native_hypothesis_census.source_snapshot.v1",
        "index_id": INDEX_ID,
        "source_root_id": source_root_id,
        "snapshot_tuple_hash": tuple_hash,
        "absolute_paths_in_snapshot_hash": False,
        "timestamps_in_snapshot_hash": False,
        "final_hash_verification": final_hash_verification,
        "records": records,
        "filename_normalization_collisions": normalized_collisions,
        "performance": {
            "files_discovered": len(records),
            "files_hashed": files_hashed,
            "files_reused_from_cache": cache_reused,
            "bytes_read_for_hashing": bytes_read,
            "elapsed_wall_seconds": round(
                time.perf_counter() - started_wall, 6
            ),
            "elapsed_cpu_seconds": round(time.process_time() - started_cpu, 6),
            "peak_memory_bytes": int(peak_memory),
            "worker_count": worker_count,
            "duplicate_groups_found": sum(
                1 for paths in hashes.values() if len(paths) > 1
            ),
            "content_extraction_failures": sum(
                1
                for row in records
                if row["content_extraction_status"]
                == "PARSER_FAILURE_PRESERVED"
            ),
        },
    }


def compare_snapshots(initial: dict[str, Any], final: dict[str, Any]) -> dict[str, Any]:
    if initial["source_root_id"] != final["source_root_id"]:
        raise CensusIndexError("snapshot root identities differ")
    initial_rows = {
        row["custody_relative_path"]: row for row in initial["records"]
    }
    final_rows = {row["custody_relative_path"]: row for row in final["records"]}
    added = sorted(set(final_rows) - set(initial_rows))
    removed = sorted(set(initial_rows) - set(final_rows))
    changed = sorted(
        path
        for path in set(initial_rows) & set(final_rows)
        if (
            initial_rows[path]["file_type"],
            initial_rows[path]["file_size"],
            initial_rows[path]["local_verified_sha256"],
            initial_rows[path]["custody_class"],
        )
        != (
            final_rows[path]["file_type"],
            final_rows[path]["file_size"],
            final_rows[path]["local_verified_sha256"],
            final_rows[path]["custody_class"],
        )
    )
    stable = not added and not removed and not changed
    return {
        "source_root_id": initial["source_root_id"],
        "initial_snapshot_tuple_hash": initial["snapshot_tuple_hash"],
        "final_snapshot_tuple_hash": final["snapshot_tuple_hash"],
        "files_added_during_execution": added,
        "files_removed_during_execution": removed,
        "files_changed_during_execution": changed,
        "stability_status": (
            "SOURCE_ROOT_SNAPSHOT_STABLE"
            if stable
            else "SOURCE_ROOT_MUTATED_DURING_CENSUS"
        ),
    }


def shard_records(
    records: list[dict[str, Any]], batch_count: int
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    if batch_count <= 0:
        raise CensusIndexError("batch count must be positive")
    ordered = sorted(
        records, key=lambda row: row["custody_relative_path"].encode("utf-8")
    )
    batches: list[dict[str, Any]] = []
    seen: set[str] = set()
    for batch_index in range(batch_count):
        batch_rows = ordered[batch_index::batch_count]
        paths = [row["custody_relative_path"] for row in batch_rows]
        if seen.intersection(paths):
            raise CensusIndexError("batch overlap detected")
        seen.update(paths)
        payload = {
            "batch_id": f"batch_{batch_index + 1:02d}",
            "records": batch_rows,
        }
        payload["batch_hash"] = sha256_bytes(jcs_bytes(payload))
        batches.append(payload)
    expected = {row["custody_relative_path"] for row in ordered}
    if seen != expected:
        raise CensusIndexError("batch union does not equal source inventory")
    aggregate = {
        "schema_id": "toe.native_hypothesis_census.batch_aggregate.v1",
        "batch_hashes": [
            {
                "batch_id": batch["batch_id"],
                "batch_hash": batch["batch_hash"],
            }
            for batch in batches
        ],
        "record_count": len(ordered),
        "coverage_without_overlap_or_omission": True,
    }
    aggregate["aggregate_hash"] = sha256_bytes(jcs_bytes(aggregate))
    return batches, aggregate


def schema_contract() -> dict[str, Any]:
    return {
        "schema_id": "toe.native_hypothesis_census.index_schema.v1",
        "index_id": INDEX_ID,
        "schema_version": INDEX_SCHEMA_VERSION,
        "hashing_schema_version": HASHING_SCHEMA_VERSION,
        "parser_contract_version": PARSER_CONTRACT_VERSION,
        "cache_status": "LOCAL_REGENERABLE_NONAUTHORITATIVE",
        "cache_never_replaces_final_hash_verification": True,
        "tracked_primary_identity": "COMMITTED_GIT_BLOB_BYTES",
        "tracked_blob_read_method": "git cat-file blob",
        "local_final_manifest_requires_verified_sha256": True,
        "metadata_is_change_detection_hint_only": True,
        "legacy_index_must_not_be_overwritten": (
            "formal/output/archive_intake_index.json"
        ),
        "stage_1_execution_enabled": False,
        "maintenance_cli_refuses_scientific_roots": True,
        "file_record_fields": [
            "source_root_id",
            "custody_relative_path",
            "git_or_filesystem_status",
            "git_object_id",
            "committed_blob_sha256",
            "worktree_sha256",
            "local_verified_sha256",
            "file_size",
            "date_metadata_with_kind_and_confidence",
            "file_type",
            "content_fingerprint",
            "duplicate_group_candidate",
            "source_classification",
            "content_extraction_status",
            "domain_tags",
            "source_lineage",
            "provenance_status",
            "licensing_or_redistribution_concern",
            "custody_class",
            "eligibility_for_deeper_review",
            "exclusion_reason",
            "source_snapshot_id",
            "indexer_schema_version",
            "parser_contract_version",
        ],
        "source_snapshot_fields": [
            "source_root_id",
            "initial_snapshot_tuple_hash",
            "final_snapshot_tuple_hash",
            "stability_status",
        ],
        "symlink_junction_reparse_policy": (
            "DO_NOT_FOLLOW_RECORD_METADATA_AND_BLOCK_ANY_ROOT_ESCAPE"
        ),
        "filename_normalization_collision_policy": (
            "PRESERVE_RAW_NAMES_RECORD_COLLISION_AND_BLOCK_AMBIGUOUS_INTAKE"
        ),
        "special_file_policy": (
            "DEVICE_PIPE_SOCKET_OR_OTHER_SPECIAL_OBJECT_METADATA_ONLY"
        ),
        "network_policy": "DENY",
        "macro_policy": "DISABLED",
        "embedded_object_policy": "NEVER_ACTIVATE_OR_EXTRACT_RECURSIVELY",
        "recursive_archive_expansion": "DENY",
        "archived_active_content_execution": "DENY",
        "batch_contract": {
            "batch_count_for_stage_1": 8,
            "batch_overlap_permitted": False,
            "batch_omission_permitted": False,
            "aggregate_manifest_binds_each_batch_hash": True,
        },
        "parser_specs": [
            {
                "parser_id": spec.parser_id,
                "extensions": list(spec.extensions),
                "max_file_bytes": spec.max_file_bytes,
                "max_extracted_text_bytes": spec.max_extracted_text_bytes,
                "timeout_seconds": spec.timeout_seconds,
                "memory_limit_bytes": spec.memory_limit_bytes,
                "maximum_nesting_or_recursion_depth": (
                    spec.maximum_nesting_or_recursion_depth
                ),
                "maximum_record_or_cell_count": (
                    spec.maximum_record_or_cell_count
                ),
                "maximum_page_or_worksheet_count": (
                    spec.maximum_page_or_worksheet_count
                ),
            }
            for spec in PARSER_SPECS
        ],
    }


def _reject_scientific_root_for_maintenance(root: Path) -> None:
    resolved = root.resolve(strict=False)
    if resolved == REPO_ROOT.resolve(strict=False):
        raise UnsafePathError("repository root is not a maintenance trial root")
    for protected in PROTECTED_SCIENTIFIC_ROOTS:
        if _inside(resolved, protected) or _inside(protected, resolved):
            raise UnsafePathError(
                "scientific archive roots require a Stage-1 OPEN event"
            )


def build_maintenance_trial(
    root: Path, cache_path: Path, source_root_id: str
) -> dict[str, Any]:
    _reject_scientific_root_for_maintenance(root)
    if LEGACY_INDEX_PATH == cache_path:
        raise CensusIndexError("legacy archive index must not be overwritten")
    with HashCache(cache_path) as cache:
        initial = build_snapshot(
            source_root_id=source_root_id,
            root=root,
            cache=cache,
            final_hash_verification=True,
            extract_text=True,
        )
        cached_trial = build_snapshot(
            source_root_id=source_root_id,
            root=root,
            cache=cache,
            final_hash_verification=False,
            extract_text=True,
        )
        final = build_snapshot(
            source_root_id=source_root_id,
            root=root,
            cache=cache,
            final_hash_verification=True,
            extract_text=True,
        )
    batches, aggregate = shard_records(final["records"], batch_count=8)
    return {
        "schema_id": "toe.native_hypothesis_census.maintenance_trial.v1",
        "authority_status": "LOCAL_REGENERABLE_NONAUTHORITATIVE",
        "scientific_census": False,
        "archive_scientifically_traversed": False,
        "initial_snapshot": initial,
        "cache_reuse_trial": cached_trial["performance"],
        "final_snapshot": final,
        "mutation_comparison": compare_snapshots(initial, final),
        "batch_manifests": batches,
        "aggregate_manifest": aggregate,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run a nonauthoritative synthetic maintenance trial. "
            "Scientific archive roots are refused."
        )
    )
    parser.add_argument("--synthetic-root", type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=DEFAULT_CACHE_PATH)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument(
        "--source-root-id", default="SYNTHETIC_MAINTENANCE_TRIAL"
    )
    args = parser.parse_args(argv)
    result = build_maintenance_trial(
        args.synthetic_root, args.cache, args.source_root_id
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
