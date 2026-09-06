from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.meta.artifact_custody import (
    ArtifactCustodyState,
    load_external_custody_index,
    snapshot_artifact,
)


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True, text=True)


def test_artifact_states_distinguish_committed_working_external_and_absent(
    tmp_path: Path,
) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init")
    tracked = repo / "tracked.json"
    tracked.write_text("{}\n", encoding="utf-8")
    _git(repo, "add", "tracked.json")
    working = repo / "working.json"
    working.write_text("{\"state\": \"local\"}\n", encoding="utf-8")

    manifest = tmp_path / "custody.json"
    manifest.write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "path": "external.json",
                        "sha256": "a" * 64,
                        "size": 17,
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    custody = load_external_custody_index(manifest)

    assert snapshot_artifact(tracked, repo_root=repo).state is ArtifactCustodyState.COMMITTED_PRESENT
    assert snapshot_artifact(working, repo_root=repo).state is ArtifactCustodyState.WORKING_TREE_ONLY
    external = snapshot_artifact(
        repo / "external.json", repo_root=repo, external_custody_index=custody
    )
    assert external.state is ArtifactCustodyState.EXTERNAL_CUSTODY_ONLY
    assert external.sha256 == "a" * 64
    assert snapshot_artifact(repo / "absent.json", repo_root=repo).state is ArtifactCustodyState.ABSENT


def test_deleted_committed_artifact_is_not_reported_as_generic_absence(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init")
    tracked = repo / "tracked.json"
    tracked.write_text("{}\n", encoding="utf-8")
    _git(repo, "add", "tracked.json")
    tracked.unlink()

    assert snapshot_artifact(tracked, repo_root=repo).state is ArtifactCustodyState.COMMITTED_MISSING
