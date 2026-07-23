from __future__ import annotations

import hashlib
import json
import subprocess
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CONTRACT_RELATIVE_PATH = (
    "formal/docs/release/"
    "QFT_ROUTE_EVIDENCE_IDENTITY_DOMAIN_CONTRACT_20260723_v0.json"
)
CONTRACT_PATH = REPO_ROOT / CONTRACT_RELATIVE_PATH
CONTRACT_SCHEMA_ID = "toe.qft_route_evidence_identity_domain_contract.v0"
FROZEN_GIT_BLOB_SHA256 = "FROZEN_GIT_BLOB_SHA256"
CANONICAL_ARTIFACT_SHA256 = "CANONICAL_ARTIFACT_SHA256"
HISTORICAL_RAW_WORKING_TREE_SHA256 = "HISTORICAL_RAW_WORKING_TREE_SHA256"
ALLOWED_CURRENT_DOMAINS = {
    FROZEN_GIT_BLOB_SHA256,
    CANONICAL_ARTIFACT_SHA256,
}


class IdentityContractError(ValueError):
    """Raised when route evidence does not satisfy its declared identity domain."""


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise IdentityContractError(message)


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
        raise IdentityContractError(
            f"Git identity lookup failed ({' '.join(args)}): {detail}"
        )
    return completed.stdout


def load_contract(contract_path: Path = CONTRACT_PATH) -> dict[str, Any]:
    _require(contract_path.is_file(), f"identity contract is missing: {contract_path}")
    raw = contract_path.read_bytes()
    try:
        contract = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise IdentityContractError(f"identity contract is invalid JSON: {exc}") from exc
    _require(
        raw == canonical_json_bytes(contract),
        "identity contract is not canonical JSON",
    )
    _require(isinstance(contract, dict), "identity contract root is not an object")
    _require(
        contract.get("schema_id") == CONTRACT_SCHEMA_ID,
        "identity contract schema is not recognized",
    )
    identities = contract.get("identities")
    _require(isinstance(identities, list), "identity contract entries are not a list")
    _require(
        contract.get("identity_count") == 9 == len(identities),
        "identity contract must contain exactly nine entries",
    )
    paths: set[str] = set()
    artifact_ids: set[str] = set()
    domain_counts = {
        FROZEN_GIT_BLOB_SHA256: 0,
        CANONICAL_ARTIFACT_SHA256: 0,
    }
    for entry in identities:
        _require(isinstance(entry, dict), "identity entry is not an object")
        path = entry.get("path")
        artifact_id = entry.get("artifact_id")
        _require(isinstance(path, str) and path, "identity path is absent")
        _require(
            isinstance(artifact_id, str) and artifact_id,
            f"identity artifact_id is absent: {path}",
        )
        _require(path not in paths, f"duplicate identity path: {path}")
        _require(
            artifact_id not in artifact_ids,
            f"duplicate identity artifact_id: {artifact_id}",
        )
        paths.add(path)
        artifact_ids.add(artifact_id)
        historical = entry.get("historical_identity")
        current = entry.get("current_identity")
        _require(
            isinstance(historical, dict)
            and historical.get("domain") == HISTORICAL_RAW_WORKING_TREE_SHA256
            and _is_sha256(historical.get("sha256")),
            f"historical identity is invalid: {path}",
        )
        _require(isinstance(current, dict), f"current identity is absent: {path}")
        domain = current.get("domain")
        _require(domain in ALLOWED_CURRENT_DOMAINS, f"identity domain is invalid: {path}")
        _require(_is_sha256(current.get("sha256")), f"SHA-256 is invalid: {path}")
        _require(_is_git_oid(current.get("git_blob_oid")), f"Git OID is invalid: {path}")
        domain_counts[domain] += 1
    _require(
        domain_counts
        == {
            FROZEN_GIT_BLOB_SHA256: 8,
            CANONICAL_ARTIFACT_SHA256: 1,
        },
        "identity contract must declare eight Git-blob and one canonical-artifact identity",
    )
    return contract


def _is_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _is_git_oid(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 40
        and all(character in "0123456789abcdef" for character in value)
    )


def _resolve_frozen_git_blob(
    entry: dict[str, Any],
    *,
    repo_root: Path,
    frozen_commit: str,
) -> dict[str, str]:
    path = entry["path"]
    current = entry["current_identity"]
    _require((repo_root / path).is_file(), f"route source is missing: {path}")
    revision = f"{frozen_commit}:{path}"
    observed_oid = _git_bytes(repo_root, "rev-parse", revision).decode("ascii").strip()
    _require(
        observed_oid == current["git_blob_oid"],
        f"frozen Git blob OID mismatch: {path}",
    )
    raw = _git_bytes(repo_root, "cat-file", "blob", observed_oid)
    _require(
        sha256_bytes(raw) == current["sha256"],
        f"frozen Git blob SHA-256 mismatch: {path}",
    )
    return {
        "artifact_id": entry["artifact_id"],
        "domain": FROZEN_GIT_BLOB_SHA256,
        "git_blob_oid": observed_oid,
        "path": path,
        "sha256": current["sha256"],
    }


def _resolve_canonical_artifact(
    entry: dict[str, Any],
    *,
    repo_root: Path,
    frozen_commit: str,
) -> dict[str, str]:
    path = entry["path"]
    current = entry["current_identity"]
    artifact_path = repo_root / path
    _require(artifact_path.is_file(), f"canonical artifact is missing: {path}")
    raw = artifact_path.read_bytes()
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise IdentityContractError(
            f"canonical artifact is invalid JSON: {path}: {exc}"
        ) from exc
    _require(
        raw == canonical_json_bytes(payload),
        f"canonical artifact serialization mismatch: {path}",
    )
    _require(
        sha256_bytes(raw) == current["sha256"],
        f"canonical artifact SHA-256 mismatch: {path}",
    )
    revision = f"{frozen_commit}:{path}"
    observed_oid = _git_bytes(repo_root, "rev-parse", revision).decode("ascii").strip()
    _require(
        observed_oid == current["git_blob_oid"],
        f"canonical artifact frozen Git OID mismatch: {path}",
    )
    return {
        "artifact_id": entry["artifact_id"],
        "domain": CANONICAL_ARTIFACT_SHA256,
        "git_blob_oid": observed_oid,
        "path": path,
        "sha256": current["sha256"],
    }


def verify_route_evidence(
    expected_paths: Iterable[str] | None = None,
    *,
    expected_historical_sha_by_path: dict[str, str] | None = None,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = CONTRACT_PATH,
) -> list[dict[str, str]]:
    contract = load_contract(contract_path)
    identities = contract["identities"]
    contract_paths = [entry["path"] for entry in identities]
    if expected_paths is not None:
        expected = list(expected_paths)
        _require(
            expected == contract_paths,
            "consumer route-evidence paths differ from the typed contract",
        )
    if expected_historical_sha_by_path is not None:
        observed_historical = {
            entry["path"]: entry["historical_identity"]["sha256"]
            for entry in identities
        }
        _require(
            observed_historical == expected_historical_sha_by_path,
            "typed contract does not preserve the consumer's historical pins",
        )
    frozen_commit = contract["frozen_commit"]
    resolved: list[dict[str, str]] = []
    for entry in identities:
        domain = entry["current_identity"]["domain"]
        if domain == FROZEN_GIT_BLOB_SHA256:
            resolved.append(
                _resolve_frozen_git_blob(
                    entry,
                    repo_root=repo_root,
                    frozen_commit=frozen_commit,
                )
            )
        elif domain == CANONICAL_ARTIFACT_SHA256:
            resolved.append(
                _resolve_canonical_artifact(
                    entry,
                    repo_root=repo_root,
                    frozen_commit=frozen_commit,
                )
            )
        else:  # load_contract makes this unreachable; keep the resolver fail-closed.
            raise IdentityContractError(f"unsupported identity domain: {domain}")
    return resolved


def bindings_match_declared_identities(
    bindings: Iterable[dict[str, Any]],
    *,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = CONTRACT_PATH,
) -> bool:
    """Validate mixed historical bindings without treating checkout EOLs as identity."""
    try:
        contract = load_contract(contract_path)
        historical_by_path = {
            entry["path"]: entry["historical_identity"]["sha256"]
            for entry in contract["identities"]
        }
        verify_route_evidence(
            repo_root=repo_root,
            contract_path=contract_path,
        )
        for binding in bindings:
            path = binding["path"]
            expected_sha256 = binding["sha256"]
            if path in historical_by_path:
                if expected_sha256 != historical_by_path[path]:
                    return False
                continue
            artifact_path = repo_root / path
            if (
                not artifact_path.is_file()
                or sha256_bytes(artifact_path.read_bytes()) != expected_sha256
            ):
                return False
    except (IdentityContractError, KeyError, OSError, TypeError):
        return False
    return True
