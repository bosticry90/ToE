from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any


def _run(repo: Path, *args: str, text: bool = False) -> bytes | str:
    completed = subprocess.run(
        ["git", *args],
        cwd=repo,
        capture_output=True,
        check=True,
        text=text,
    )
    return completed.stdout


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def build_manifest(repo: Path) -> tuple[dict[str, Any], bytes]:
    raw_status = _run(repo, "status", "--porcelain=v1", "-z", "--untracked-files=all")
    assert isinstance(raw_status, bytes)
    rows: list[dict[str, Any]] = []
    for item in raw_status.split(b"\0"):
        if not item:
            continue
        status = item[:2].decode("ascii", errors="replace")
        relative = item[3:].decode("utf-8", errors="surrogateescape")
        path = repo / relative
        working = path.read_bytes() if path.is_file() else b""
        head_result = subprocess.run(
            ["git", "show", f"HEAD:{relative}"],
            cwd=repo,
            capture_output=True,
            check=False,
        )
        rows.append(
            {
                "path": relative,
                "status": status,
                "working_exists": path.exists(),
                "working_size": len(working) if path.is_file() else None,
                "working_sha256": _sha(working) if path.is_file() else None,
                "head_exists": head_result.returncode == 0,
                "head_size": len(head_result.stdout)
                if head_result.returncode == 0
                else None,
                "head_sha256": _sha(head_result.stdout)
                if head_result.returncode == 0
                else None,
            }
        )
    diff = _run(repo, "diff", "--binary", "--no-ext-diff")
    assert isinstance(diff, bytes)
    tracked_dirty = [row for row in rows if row["status"] != "??"]
    return (
        {
            "schema_id": "CLEAN_BASELINE_POST_VALIDATION_MUTATION_MANIFEST_20260720_v0",
            "source_commit": str(_run(repo, "rev-parse", "HEAD", text=True)).strip(),
            "validation_clone": repo.as_posix(),
            "working_tree_clean_after_validation": not rows,
            "dirty_entry_count": len(rows),
            "tracked_dirty_count": len(tracked_dirty),
            "untracked_count": len(rows) - len(tracked_dirty),
            "entries": rows,
            "binary_diff_sha256": _sha(diff),
            "classification": "VALIDATION_COMMAND_MUTATED_BASELINE_CLONE"
            if tracked_dirty
            else "NO_TRACKED_MUTATION",
            "scientific_status_changed": False,
        },
        diff,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    manifest, diff = build_manifest(args.repo.resolve())
    (args.out_dir / "CLEAN_BASELINE_POST_VALIDATION_MUTATION_MANIFEST_v0.json").write_bytes(
        _canonical(manifest)
    )
    (args.out_dir / "CLEAN_BASELINE_POST_VALIDATION_MUTATIONS_v0.patch").write_bytes(diff)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
