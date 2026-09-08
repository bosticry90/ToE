from __future__ import annotations

import hashlib
import subprocess
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable


EM_PATH = "formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
EM_ACCEPTED_HISTORICAL_SHA256 = (
    "7b1c0bdd683e5d5891a77cf27772df239967ca210b3a7c9fd88ba75f7a1e85e9"
)
EM_HISTORICAL_CR_INSERT_OFFSET = 92149


class StagingIdentityError(ValueError):
    """Raised when historical staging bytes lack a reviewed identity route."""


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


@lru_cache(maxsize=None)
def _git_bytes(repo_root: Path, *args: str) -> bytes:
    completed = subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise StagingIdentityError(
            f"Git staging identity lookup failed ({' '.join(args)}): {detail}"
        )
    return completed.stdout


def git_blob(repo_root: Path, commit: str, path: str) -> tuple[str, bytes]:
    oid = _git_bytes(repo_root, "rev-parse", f"{commit}:{path}").decode(
        "ascii"
    ).strip()
    return oid, _git_bytes(repo_root, "cat-file", "blob", oid)


def historical_representation(
    *,
    repo_root: Path,
    commit: str,
    path: str,
    expected_sha256: str,
) -> dict[str, Any]:
    oid, blob = git_blob(repo_root, commit, path)
    candidates: list[tuple[str, bytes]] = [
        ("GIT_BLOB_EXACT", blob),
        (
            "CRLF_FROM_FROZEN_GIT_BLOB",
            blob.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n"),
        ),
    ]
    if path == EM_PATH and expected_sha256 == EM_ACCEPTED_HISTORICAL_SHA256:
        candidates.append(
            (
                "ACCEPTED_MIXED_EOL_RECONSTRUCTION",
                blob[:EM_HISTORICAL_CR_INSERT_OFFSET]
                + b"\r"
                + blob[EM_HISTORICAL_CR_INSERT_OFFSET:],
            )
        )
    for representation, raw in candidates:
        if sha256_bytes(raw) == expected_sha256:
            return {
                "path": path,
                "commit": commit,
                "git_blob": oid,
                "git_blob_sha256": sha256_bytes(blob),
                "historical_pin_sha256": expected_sha256,
                "representation": representation,
                "bytes": raw,
            }
    raise StagingIdentityError(
        f"historical pin is not reconstructible from an accepted identity: {path}"
    )


def bindings_match_historical_identities(
    bindings: Iterable[dict[str, Any]],
    *,
    repo_root: Path,
    commit: str,
) -> bool:
    try:
        for binding in bindings:
            historical_representation(
                repo_root=repo_root,
                commit=commit,
                path=binding["path"],
                expected_sha256=binding["sha256"],
            )
    except (KeyError, OSError, StagingIdentityError, TypeError):
        return False
    return True


def historical_source_text(
    *,
    repo_root: Path,
    commit: str,
    path: str,
) -> str:
    _, blob = git_blob(repo_root, commit, path)
    return blob.decode("utf-8")


def materialize_historical_tree(
    root: Path,
    *,
    repo_root: Path,
    commit: str,
    frozen_hashes: dict[str, str],
    runtime_paths: Iterable[str],
) -> list[dict[str, Any]]:
    resolved: list[dict[str, Any]] = []
    for path, expected_sha256 in frozen_hashes.items():
        identity = historical_representation(
            repo_root=repo_root,
            commit=commit,
            path=path,
            expected_sha256=expected_sha256,
        )
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(identity.pop("bytes"))
        resolved.append(identity)
    for path in runtime_paths:
        oid, blob = git_blob(repo_root, commit, path)
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(blob)
        resolved.append(
            {
                "path": path,
                "commit": commit,
                "git_blob": oid,
                "git_blob_sha256": sha256_bytes(blob),
                "historical_pin_sha256": sha256_bytes(blob),
                "representation": "GIT_BLOB_EXACT",
            }
        )
    return resolved
