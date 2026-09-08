from __future__ import annotations

import hashlib
import json
import subprocess
from functools import lru_cache
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CONTRACT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EQUATION_COMPENDIUM_IDENTITY_DOMAIN_CONTRACT_20260724_v0.json"
)
CONTRACT_PATH = REPO_ROOT / CONTRACT_RELATIVE_PATH
CONTRACT_SCHEMA_ID = "toe.equation_compendium_identity_domain_contract.v0"
COMPENDIUM_RELATIVE_PATH = (
    "formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
)
FROZEN_GIT_BLOB_SHA256 = "FROZEN_GIT_BLOB_SHA256"
HISTORICAL_MIXED_EOL_WORKING_TREE_SHA256 = (
    "HISTORICAL_MIXED_EOL_WORKING_TREE_SHA256"
)


class IdentityContractError(ValueError):
    """Raised when the compendium fails its declared identity contract."""


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise IdentityContractError(message)


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
    _require(
        contract.get("identity_count") == 1,
        "identity contract must contain exactly one entry",
    )
    _require(
        _is_git_oid(contract.get("frozen_commit")),
        "identity contract frozen commit is invalid",
    )
    identity = contract.get("identity")
    _require(isinstance(identity, dict), "identity entry is absent")
    path = identity.get("path")
    _require(
        path == COMPENDIUM_RELATIVE_PATH,
        "identity path is absent or not the equation compendium",
    )
    historical = identity.get("historical_identity")
    _require(
        isinstance(historical, dict)
        and historical.get("domain")
        == HISTORICAL_MIXED_EOL_WORKING_TREE_SHA256
        and _is_sha256(historical.get("sha256"))
        and historical.get("bytes") == 13743
        and historical.get("line_feeds") == 113
        and historical.get("carriage_returns") == 85,
        "historical mixed-EOL identity is invalid",
    )
    current = identity.get("current_identity")
    _require(
        isinstance(current, dict)
        and current.get("domain") == FROZEN_GIT_BLOB_SHA256
        and _is_git_oid(current.get("git_blob_oid"))
        and _is_sha256(current.get("sha256"))
        and current.get("bytes") == 13658,
        "current frozen Git-blob identity is invalid",
    )
    return contract


def verify_equation_compendium(
    *,
    expected_path: str | None = None,
    expected_historical_sha256: str | None = None,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = CONTRACT_PATH,
) -> dict[str, str | int]:
    """Resolve the current compendium from Git while preserving its old raw pin."""

    contract = load_contract(contract_path)
    identity = contract["identity"]
    path = identity["path"]
    historical = identity["historical_identity"]
    current = identity["current_identity"]
    if expected_path is not None:
        _require(
            expected_path == path,
            "consumer compendium path differs from the typed contract",
        )
    if expected_historical_sha256 is not None:
        _require(
            expected_historical_sha256 == historical["sha256"],
            "typed contract does not preserve the consumer's historical pin",
        )
    _require((repo_root / path).is_file(), f"equation compendium is missing: {path}")
    revision = f"{contract['frozen_commit']}:{path}"
    observed_oid = _git_bytes(repo_root, "rev-parse", revision).decode("ascii").strip()
    _require(
        observed_oid == current["git_blob_oid"],
        "frozen equation-compendium Git blob OID mismatch",
    )
    raw = _git_bytes(repo_root, "cat-file", "blob", observed_oid)
    _require(
        len(raw) == current["bytes"],
        "frozen equation-compendium Git blob size mismatch",
    )
    _require(
        sha256_bytes(raw) == current["sha256"],
        "frozen equation-compendium Git blob SHA-256 mismatch",
    )
    return {
        "artifact_id": identity["artifact_id"],
        "bytes": current["bytes"],
        "domain": FROZEN_GIT_BLOB_SHA256,
        "git_blob_oid": observed_oid,
        "historical_sha256": historical["sha256"],
        "path": path,
        "sha256": current["sha256"],
    }
