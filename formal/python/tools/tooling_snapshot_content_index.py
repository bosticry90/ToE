from __future__ import annotations

import argparse
import json
import subprocess
from collections import defaultdict
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SNAPSHOT_ROOT = REPO_ROOT / "formal" / "tooling_snapshots"
OUTPUT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOOLING_SNAPSHOT_CONTENT_INDEX_20260711_v0.json"
)


def _git(*args: str) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout


def tracked_snapshot_entries() -> list[dict[str, Any]]:
    worktree_status = _git(
        "status",
        "--porcelain=v1",
        "--untracked-files=no",
        "--",
        "formal/tooling_snapshots",
    )
    if worktree_status.strip():
        raise ValueError(
            "tooling snapshot worktree differs from the Git index; refuse mixed provenance"
        )

    pending: list[dict[str, Any]] = []
    output = _git("ls-files", "-s", "--", "formal/tooling_snapshots")
    for line in output.splitlines():
        if not line.strip():
            continue
        metadata, path_text = line.split("\t", 1)
        mode, object_id, stage = metadata.split()
        path = REPO_ROOT / path_text
        if not path.is_file():
            raise ValueError(f"tracked snapshot path is missing: {path_text}")
        pending.append(
            {
                "git_blob_object_id": object_id,
                "git_mode": mode,
                "git_stage": int(stage),
                "path": path_text.replace("\\", "/"),
            }
        )

    object_ids = sorted({row["git_blob_object_id"] for row in pending})
    completed = subprocess.run(
        ["git", "cat-file", "--batch-check=%(objectname) %(objecttype) %(objectsize)"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
        input="\n".join(object_ids) + "\n",
    )
    object_sizes: dict[str, int] = {}
    for line in completed.stdout.splitlines():
        object_id, object_type, size_text = line.split()
        if object_type != "blob":
            raise ValueError(f"snapshot object is not a blob: {object_id} {object_type}")
        object_sizes[object_id] = int(size_text)
    if set(object_sizes) != set(object_ids):
        raise ValueError("Git cat-file did not return every snapshot blob")

    entries = [
        {**row, "size_bytes": object_sizes[row["git_blob_object_id"]]}
        for row in pending
    ]
    entries.sort(key=lambda row: row["path"])
    return entries


def build_index() -> dict[str, Any]:
    entries = tracked_snapshot_entries()
    by_object: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for entry in entries:
        by_object[entry["git_blob_object_id"]].append(entry)

    duplicate_groups: list[dict[str, Any]] = []
    redundant_bytes = 0
    for object_id, rows in sorted(by_object.items()):
        if len(rows) < 2:
            continue
        size = rows[0]["size_bytes"]
        if any(row["size_bytes"] != size for row in rows):
            raise ValueError(f"same Git object has inconsistent sizes: {object_id}")
        group_redundancy = size * (len(rows) - 1)
        redundant_bytes += group_redundancy
        duplicate_groups.append(
            {
                "canonical_path": rows[0]["path"],
                "duplicate_paths": [row["path"] for row in rows[1:]],
                "git_blob_object_id": object_id,
                "path_count": len(rows),
                "redundant_worktree_bytes": group_redundancy,
                "size_bytes": size,
            }
        )

    return {
        "boundary": {
            "artifact_deletion_authorized": False,
            "authority_or_scientific_claim_changed": False,
            "content_addressed_migration_executed": False,
            "historical_paths_preserved": True,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "duplicate_groups": duplicate_groups,
        "entries": entries,
        "git_object_format": _git("rev-parse", "--show-object-format").strip(),
        "source_snapshot_tree_object_id": _git(
            "rev-parse", "HEAD:formal/tooling_snapshots"
        ).strip(),
        "source_tree_rule": (
            "Blob IDs and sizes come from the Git index/object database; generation "
            "fails when tracked snapshot worktree content is modified."
        ),
        "metrics": {
            "duplicate_group_count": len(duplicate_groups),
            "redundant_worktree_bytes": redundant_bytes,
            "tracked_snapshot_bytes": sum(row["size_bytes"] for row in entries),
            "tracked_snapshot_path_count": len(entries),
            "unique_blob_count": len(by_object),
        },
        "schema_id": "TOOLING_SNAPSHOT_CONTENT_INDEX_20260711_v0",
        "status": "INVENTORY_ONLY_PROVENANCE_PRESERVED_NO_DELETION_AUTHORIZED",
    }


def canonical_bytes(payload: dict[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Index tracked tooling snapshots by Git blob.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="Fail when the index is stale (default).")
    mode.add_argument("--write", action="store_true", help="Write the deterministic index.")
    args = parser.parse_args()

    expected = canonical_bytes(build_index())
    current = OUTPUT_PATH.read_bytes() if OUTPUT_PATH.exists() else None
    if args.write:
        if current != expected:
            OUTPUT_PATH.write_bytes(expected)
            print("tooling_snapshot_content_index: wrote index")
        else:
            print("tooling_snapshot_content_index: already current")
        return 0
    if current != expected:
        print("tooling_snapshot_content_index: FAILED index drift")
        return 1
    print("tooling_snapshot_content_index: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
