from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CONTRACT_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "ADMISSIBILITY_MANIFEST_CURRENT_IDENTITY_CONTRACT_20260725_v0.json"
)


class IdentityError(ValueError):
    """Raised when a commit-relative admissibility identity is invalid."""


def load_contract() -> dict[str, Any]:
    payload = json.loads(CONTRACT_PATH.read_bytes())
    if payload.get("identity_algorithm") != "SHA256(GIT_BLOB_CONTENTS)":
        raise IdentityError("unsupported admissibility identity algorithm")
    return payload


def resolve_binding(commit: str, path: str) -> tuple[str, str]:
    oid = subprocess.run(
        ["git", "rev-parse", f"{commit}:{path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=True,
        text=True,
    ).stdout.strip()
    raw = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=True,
    ).stdout
    return oid, hashlib.sha256(raw).hexdigest()


def validate_contract() -> dict[str, dict[str, str]]:
    contract = load_contract()
    commit = contract["current_relative_to_commit"]
    bindings = contract["bindings"]
    if len(bindings) != 15:
        raise IdentityError("admissibility contract must contain 15 bindings")
    resolved: dict[str, dict[str, str]] = {}
    for binding in bindings:
        path = binding["path"]
        if path in resolved:
            raise IdentityError(f"duplicate admissibility path: {path}")
        oid, sha256 = resolve_binding(commit, path)
        if oid != binding["git_blob"] or sha256 != binding["sha256"]:
            raise IdentityError(f"admissibility identity mismatch: {path}")
        resolved[path] = {
            "git_blob": oid,
            "sha256": sha256,
            "role": binding["role"],
        }
    return resolved
