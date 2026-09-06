from __future__ import annotations

import hashlib
import json
import subprocess
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Iterable


class ArtifactCustodyState(str, Enum):
    COMMITTED_PRESENT = "COMMITTED_PRESENT"
    COMMITTED_MISSING = "COMMITTED_MISSING"
    WORKING_TREE_ONLY = "WORKING_TREE_ONLY"
    EXTERNAL_CUSTODY_ONLY = "EXTERNAL_CUSTODY_ONLY"
    ABSENT = "ABSENT"


@dataclass(frozen=True)
class ArtifactSnapshot:
    path: str
    state: ArtifactCustodyState
    sha256: str | None
    size: int | None


def _relative(path: Path, repo_root: Path) -> str:
    return path.resolve().relative_to(repo_root.resolve()).as_posix()


def _is_tracked(relative_path: str, repo_root: Path) -> bool:
    result = subprocess.run(
        ["git", "ls-files", "--error-unmatch", "--", relative_path],
        cwd=str(repo_root),
        check=False,
        capture_output=True,
        text=True,
    )
    return result.returncode == 0


def load_external_custody_index(manifest_path: Path | None) -> dict[str, dict[str, Any]]:
    if manifest_path is None or not manifest_path.is_file():
        return {}
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    return {
        entry["path"]: entry
        for entry in payload.get("entries", [])
        if isinstance(entry, dict) and isinstance(entry.get("path"), str)
    }


def snapshot_artifact(
    path: Path,
    *,
    repo_root: Path,
    external_custody_index: dict[str, dict[str, Any]] | None = None,
) -> ArtifactSnapshot:
    """Classify an artifact without collapsing custody-only state into missing state."""
    relative_path = _relative(path, repo_root)
    tracked = _is_tracked(relative_path, repo_root)
    if path.is_file():
        data = path.read_bytes()
        state = (
            ArtifactCustodyState.COMMITTED_PRESENT
            if tracked
            else ArtifactCustodyState.WORKING_TREE_ONLY
        )
        return ArtifactSnapshot(
            path=relative_path,
            state=state,
            sha256=hashlib.sha256(data).hexdigest(),
            size=len(data),
        )
    if tracked:
        return ArtifactSnapshot(
            path=relative_path,
            state=ArtifactCustodyState.COMMITTED_MISSING,
            sha256=None,
            size=None,
        )
    custody_entry = (external_custody_index or {}).get(relative_path)
    if custody_entry is not None:
        return ArtifactSnapshot(
            path=relative_path,
            state=ArtifactCustodyState.EXTERNAL_CUSTODY_ONLY,
            sha256=custody_entry.get("sha256"),
            size=custody_entry.get("size"),
        )
    return ArtifactSnapshot(
        path=relative_path,
        state=ArtifactCustodyState.ABSENT,
        sha256=None,
        size=None,
    )


def snapshot_artifacts(
    paths: Iterable[Path],
    *,
    repo_root: Path,
    external_custody_index: dict[str, dict[str, Any]] | None = None,
) -> dict[str, ArtifactSnapshot]:
    return {
        snapshot.path: snapshot
        for snapshot in (
            snapshot_artifact(
                path,
                repo_root=repo_root,
                external_custody_index=external_custody_index,
            )
            for path in paths
        )
    }
