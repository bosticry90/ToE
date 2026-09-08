from __future__ import annotations

import hashlib
import json
import subprocess
from functools import lru_cache
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.equation_compendium_identity import (
    verify_equation_compendium,
)


REPO_ROOT = find_repo_root(Path(__file__))
CONTRACT_RELATIVE_PATH = (
    "formal/docs/release/"
    "PILLAR_HISTORICAL_ARTIFACT_CURRENCY_ROLE_CONTRACT_20260724_v0.json"
)
CONTRACT_PATH = REPO_ROOT / CONTRACT_RELATIVE_PATH
CONTRACT_SCHEMA_ID = "toe.pillar_historical_artifact_currency_role_contract.v0"

HISTORICAL_GENERATOR_PIN = "HISTORICAL_GENERATOR_PIN"
HISTORICAL_SOURCE_BLOB = "HISTORICAL_SOURCE_BLOB"
CURRENT_CANONICAL_IDENTITY = "CURRENT_CANONICAL_IDENTITY"
REVIEW_TIME_AUTHORITY = "REVIEW_TIME_AUTHORITY"
CURRENT_LIVE_AUTHORITY = "CURRENT_LIVE_AUTHORITY"
ALLOWED_ROLES = {
    HISTORICAL_GENERATOR_PIN,
    HISTORICAL_SOURCE_BLOB,
    CURRENT_CANONICAL_IDENTITY,
    REVIEW_TIME_AUTHORITY,
    CURRENT_LIVE_AUTHORITY,
}


class HistoricalArtifactIdentityError(ValueError):
    """Raised when a historical/current role contract cannot be verified."""


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise HistoricalArtifactIdentityError(message)


def _is_hex(value: Any, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


@lru_cache(maxsize=None)
def _git(repo_root: Path, *args: str) -> bytes:
    completed = subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise HistoricalArtifactIdentityError(
            f"Git identity lookup failed ({' '.join(args)}): {detail}"
        )
    return completed.stdout


def load_contract(contract_path: Path = CONTRACT_PATH) -> dict[str, Any]:
    _require(contract_path.is_file(), f"role contract is missing: {contract_path}")
    raw = contract_path.read_bytes()
    try:
        contract = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise HistoricalArtifactIdentityError(
            f"role contract is invalid JSON: {exc}"
        ) from exc
    _require(raw == canonical_json_bytes(contract), "role contract is not canonical JSON")
    _require(isinstance(contract, dict), "role contract root is not an object")
    _require(
        contract.get("schema_id") == CONTRACT_SCHEMA_ID,
        "role contract schema is not recognized",
    )
    identities = contract.get("identities")
    bindings = contract.get("bindings")
    _require(
        isinstance(identities, dict)
        and contract.get("identity_count") == len(identities) == 4,
        "role contract must contain exactly four identities",
    )
    _require(
        isinstance(bindings, list)
        and contract.get("binding_count") == len(bindings) == 17,
        "role contract must contain exactly seventeen bindings",
    )
    expected_ids = [f"PAC-{index:03d}" for index in range(1, 18)]
    _require(
        [binding.get("binding_id") for binding in bindings] == expected_ids,
        "role contract binding IDs are incomplete or out of order",
    )
    for binding in bindings:
        _require(
            binding.get("identity_id") in identities,
            f"unknown identity for {binding.get('binding_id')}",
        )
        _require(
            binding.get("role") in ALLOWED_ROLES
            and binding.get("current_successor_role") in ALLOWED_ROLES,
            f"unknown role for {binding.get('binding_id')}",
        )
        _require(
            _is_hex(binding.get("expected_historical_sha256"), 64),
            f"invalid historical SHA-256 for {binding.get('binding_id')}",
        )
    _require(contract.get("registry_rotated") is False, "registry rotation is forbidden")
    _require(
        contract.get("scientific_content_changed") is False,
        "scientific content change is forbidden",
    )
    _require(
        contract.get("v2_enrollment_authorized") is False,
        "V2 enrollment is forbidden",
    )
    return contract


def _binding(contract: dict[str, Any], binding_id: str) -> dict[str, Any]:
    matches = [
        binding
        for binding in contract["bindings"]
        if binding["binding_id"] == binding_id
    ]
    _require(len(matches) == 1, f"binding is absent or duplicated: {binding_id}")
    return matches[0]


def _verify_frozen_git_blob(
    identity: dict[str, Any], *, repo_root: Path
) -> dict[str, Any]:
    commit = identity.get("frozen_commit")
    path = identity.get("path")
    oid = identity.get("git_blob_oid")
    expected_sha256 = identity.get("sha256")
    _require(_is_hex(commit, 40), "frozen commit is invalid")
    _require(isinstance(path, str) and path, "frozen path is invalid")
    _require(_is_hex(oid, 40), "frozen Git blob OID is invalid")
    _require(_is_hex(expected_sha256, 64), "frozen SHA-256 is invalid")
    observed_oid = _git(repo_root, "rev-parse", f"{commit}:{path}").decode().strip()
    _require(observed_oid == oid, f"frozen Git blob OID mismatch: {path}")
    raw = _git(repo_root, "cat-file", "blob", oid)
    _require(len(raw) == identity.get("bytes"), f"frozen byte size mismatch: {path}")
    _require(
        sha256_bytes(raw) == expected_sha256,
        f"frozen Git blob SHA-256 mismatch: {path}",
    )
    return {
        "bytes": len(raw),
        "domain": "FROZEN_GIT_BLOB_SHA256",
        "frozen_commit": commit,
        "git_blob_oid": oid,
        "path": path,
        "sha256": expected_sha256,
    }


def verify_binding(
    binding_id: str,
    *,
    expected_path: str | None = None,
    expected_sha256: str | None = None,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = CONTRACT_PATH,
) -> dict[str, Any]:
    contract = load_contract(contract_path)
    binding = _binding(contract, binding_id)
    identity = contract["identities"][binding["identity_id"]]
    if expected_path is not None:
        _require(identity.get("path") == expected_path, "consumer path differs from role contract")
    if expected_sha256 is not None:
        _require(
            binding["expected_historical_sha256"] == expected_sha256,
            "consumer historical pin differs from role contract",
        )

    resolution = identity.get("resolution")
    if resolution == "FROZEN_GIT_BLOB":
        resolved = _verify_frozen_git_blob(identity, repo_root=repo_root)
    elif resolution == "EQUATION_COMPENDIUM_DOMAIN_CONTRACT":
        current = verify_equation_compendium(
            expected_path=identity["path"],
            expected_historical_sha256=identity["historical_sha256"],
            repo_root=repo_root,
        )
        resolved = {
            "bytes": identity["historical_bytes"],
            "current_canonical_identity": current,
            "domain": identity["historical_domain"],
            "path": identity["path"],
            "sha256": identity["historical_sha256"],
        }
    elif resolution == "REVIEW_TIME_GIT_BLOB_WITH_LIVE_SUCCESSOR":
        historical = _verify_frozen_git_blob(identity, repo_root=repo_root)
        live_path = repo_root / identity["path"]
        _require(live_path.is_file(), f"current live authority is missing: {live_path}")
        resolved = {
            **historical,
            "current_live_authority_sha256": sha256_bytes(live_path.read_bytes()),
            "equality_with_current_live_authority_required": identity[
                "equality_with_current_live_authority_required"
            ],
        }
        _require(
            resolved["equality_with_current_live_authority_required"] is False,
            "review-time/live-authority equality must not be required",
        )
    else:
        raise HistoricalArtifactIdentityError(
            f"unsupported identity resolution: {resolution}"
        )

    _require(
        resolved["sha256"] == binding["expected_historical_sha256"],
        f"resolved historical SHA-256 mismatch: {binding_id}",
    )
    return {
        **resolved,
        "binding_id": binding_id,
        "current_successor_role": binding["current_successor_role"],
        "identity_id": binding["identity_id"],
        "role": binding["role"],
    }


def historical_compendium_sha256_for_path(
    path: Path,
    *,
    expected_historical_sha256: str,
    repo_root: Path = REPO_ROOT,
) -> str:
    """Return the preserved historical pin for canonical LF/CRLF source bytes.

    A modified temporary copy retains its actual raw SHA-256 so negative controls
    remain fail-closed.
    """

    resolved = verify_binding(
        "PAC-007",
        expected_path=(
            "formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
        ),
        expected_sha256=expected_historical_sha256,
        repo_root=repo_root,
    )
    raw = path.read_bytes()
    normalized = raw.replace(b"\r\n", b"\n")
    current_sha256 = resolved["current_canonical_identity"]["sha256"]
    if sha256_bytes(normalized) == current_sha256:
        return resolved["sha256"]
    return sha256_bytes(raw)
