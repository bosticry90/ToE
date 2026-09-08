from __future__ import annotations

import hashlib
import json
import re
import subprocess
from functools import lru_cache
from pathlib import Path
from typing import Any


ADJUDICATION_RELATIVE_PATH = (
    "formal/docs/release/PROMPT_DEPENDENCY_ROLE_ADJUDICATION_20260722_v0.json"
)
ADJUDICATION_SCHEMA_ID = "PROMPT_DEPENDENCY_ROLE_ADJUDICATION_20260722_v0"
DEMOTED_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"


def prompt_dependency_is_nonblocking(role: str) -> bool:
    return role == DEMOTED_ROLE


@lru_cache(maxsize=None)
def _adjudication(repo_root: Path) -> dict[str, Any]:
    payload = json.loads(
        (repo_root / ADJUDICATION_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if payload.get("schema_id") != ADJUDICATION_SCHEMA_ID:
        raise ValueError("invalid Prompt dependency adjudication record")
    if payload.get("consumer_count") != 43:
        raise ValueError("Prompt dependency adjudication is not exhaustive")
    consumers = payload.get("consumers")
    if not isinstance(consumers, list) or len(consumers) != 43:
        raise ValueError("Prompt dependency consumer inventory is incomplete")
    paths = [item.get("consumer_path") for item in consumers]
    if len(set(paths)) != 43 or not all(isinstance(path, str) for path in paths):
        raise ValueError("Prompt dependency consumer paths are not unique strings")
    return payload


@lru_cache(maxsize=None)
def _frozen_semantic_source_paths(repo_root: Path) -> dict[str, str]:
    paths: dict[str, str] = {}
    for item in _adjudication(repo_root)["consumers"]:
        if item.get("disposition") != DEMOTED_ROLE:
            continue
        binding = item.get("frozen_semantic_source_identity")
        if not isinstance(binding, dict):
            raise ValueError("demoted consumer lacks frozen semantic source identity")
        commit = binding.get("commit")
        path = binding.get("path")
        if (
            not isinstance(commit, str)
            or not re.fullmatch(r"[0-9a-f]{40}", commit)
            or path != item.get("consumer_path")
        ):
            raise ValueError("invalid frozen semantic source identity")
        paths[path] = commit
    test_bindings = _adjudication(repo_root).get(
        "modified_test_obligation_source_identities"
    )
    if not isinstance(test_bindings, list) or len(test_bindings) != 39:
        raise ValueError("expected 39 modified Prompt test obligations")
    for binding in test_bindings:
        commit = binding.get("commit")
        path = binding.get("path")
        if (
            not isinstance(commit, str)
            or not re.fullmatch(r"[0-9a-f]{40}", commit)
            or not isinstance(path, str)
            or not path.startswith("formal/python/tests/")
        ):
            raise ValueError("invalid frozen test-obligation source identity")
        paths[path] = commit
    if len(paths) != 80:
        raise ValueError("expected 80 frozen maintenance source identities")
    return paths


@lru_cache(maxsize=None)
def _git_blob_bytes(repo_root: Path, commit: str, relative_path: str) -> bytes:
    result = subprocess.run(
        ["git", "cat-file", "blob", f"{commit}:{relative_path}"],
        cwd=repo_root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise ValueError(f"missing frozen semantic source blob: {commit}:{relative_path}")
    return result.stdout


def identity_sha256_path(path: Path, *, repo_root: Path) -> str:
    resolved_root = repo_root.resolve()
    resolved_path = path.resolve()
    try:
        relative_path = resolved_path.relative_to(resolved_root).as_posix()
    except ValueError:
        return hashlib.sha256(resolved_path.read_bytes()).hexdigest()
    frozen_commit = _frozen_semantic_source_paths(resolved_root).get(relative_path)
    raw = (
        _git_blob_bytes(resolved_root, frozen_commit, relative_path)
        if frozen_commit is not None
        else resolved_path.read_bytes()
    )
    return hashlib.sha256(raw).hexdigest()
