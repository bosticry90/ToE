from __future__ import annotations

import hashlib
import json
import subprocess
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qft_route_evidence_identity


REPO_ROOT = find_repo_root(Path(__file__))
CONTRACT_RELATIVE_PATH = (
    "formal/docs/release/"
    "PILLAR_V1_HISTORICAL_CURRENT_SOURCE_IDENTITY_CONTRACT_20260725_v1.json"
)
CONTRACT_PATH = REPO_ROOT / CONTRACT_RELATIVE_PATH
PREVIOUS_CONTRACT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "PILLAR_V1_HISTORICAL_CURRENT_SOURCE_IDENTITY_CONTRACT_20260725_v0.json"
)
CONTRACT_SCHEMA_ID = "toe.pillar_v1_historical_current_source_identity_contract.v1"
CONTRACT_SCHEMA_BY_VERSION = {
    "v0": "toe.pillar_v1_historical_current_source_identity_contract.v0",
    "v1": CONTRACT_SCHEMA_ID,
}
IDENTITY_ALGORITHM = "SHA-256_OF_GIT_BLOB_BYTES"
IDENTITY_ALGORITHM_VERSION = "v1"
FROZEN_REVIEW_ROLE = "V1_FROZEN_REVIEW_SOURCE_PIN"
CURRENT_SOURCE_ROLE = "CURRENT_SOURCE_BLOB_IDENTITY"
CURRENT_GENERATOR_ROLE = "CURRENT_GENERATOR_IDENTITY"
EXPECTED_ROLES = {
    FROZEN_REVIEW_ROLE: "HISTORICAL",
    CURRENT_SOURCE_ROLE: "CURRENT",
    CURRENT_GENERATOR_ROLE: "CURRENT",
}


class PillarV1IdentityContractError(ValueError):
    """Raised when a Pillar V1 source identity contract is not satisfied."""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise PillarV1IdentityContractError(message)


def _is_hex(value: Any, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
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
        raise PillarV1IdentityContractError(
            f"Git identity lookup failed ({' '.join(args)}): {detail}"
        )
    return completed.stdout


def load_contract(contract_path: Path = CONTRACT_PATH) -> dict[str, Any]:
    _require(contract_path.is_file(), f"identity contract is missing: {contract_path}")
    raw = contract_path.read_bytes()
    try:
        contract = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise PillarV1IdentityContractError(
            f"identity contract is invalid JSON: {exc}"
        ) from exc
    _require(raw == canonical_json_bytes(contract), "identity contract is not canonical JSON")
    _require(isinstance(contract, dict), "identity contract root is not an object")
    _require(
        contract.get("schema_id")
        == CONTRACT_SCHEMA_BY_VERSION.get(contract.get("contract_version")),
        "identity contract schema or version is not recognized",
    )
    _require(
        contract.get("identity_count") == 3,
        "identity contract must declare exactly three identities",
    )
    _require(
        _is_hex(contract.get("current_relative_to_commit"), 40),
        "current-relative commit is invalid",
    )
    identities = contract.get("identities")
    _require(isinstance(identities, list) and len(identities) == 3, "identity entries are invalid")
    by_role: dict[str, dict[str, Any]] = {}
    for entry in identities:
        _require(isinstance(entry, dict), "identity entry is not an object")
        role = entry.get("identity_role")
        _require(role in EXPECTED_ROLES, f"unexpected identity role: {role}")
        _require(role not in by_role, f"duplicate identity role: {role}")
        _require(
            entry.get("temporal_role") == EXPECTED_ROLES[role],
            f"temporal role mismatch: {role}",
        )
        _require(
            entry.get("identity_algorithm") == IDENTITY_ALGORITHM
            and entry.get("identity_algorithm_version") == IDENTITY_ALGORITHM_VERSION,
            f"identity algorithm mismatch: {role}",
        )
        _require(_is_hex(entry.get("relative_to_commit"), 40), f"commit is invalid: {role}")
        _require(_is_hex(entry.get("git_blob"), 40), f"Git blob is invalid: {role}")
        _require(_is_hex(entry.get("sha256"), 64), f"SHA-256 is invalid: {role}")
        _require(
            isinstance(entry.get("tracked_path"), str) and entry["tracked_path"],
            f"tracked path is invalid: {role}",
        )
        if role != FROZEN_REVIEW_ROLE:
            _require(
                entry["relative_to_commit"] == contract["current_relative_to_commit"],
                f"current identity is not relative to the contract commit: {role}",
            )
        by_role[role] = entry
    _require(set(by_role) == set(EXPECTED_ROLES), "required identity roles are incomplete")
    _require(
        by_role[FROZEN_REVIEW_ROLE]["tracked_path"]
        == by_role[CURRENT_SOURCE_ROLE]["tracked_path"],
        "historical and current source identities do not name the same tracked path",
    )
    return contract


def verify_contract(
    *,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = CONTRACT_PATH,
) -> dict[str, dict[str, Any]]:
    contract = load_contract(contract_path)
    by_role = {entry["identity_role"]: entry for entry in contract["identities"]}
    for role, entry in by_role.items():
        revision = f"{entry['relative_to_commit']}:{entry['tracked_path']}"
        observed_blob = _git_bytes(repo_root, "rev-parse", revision).decode("ascii").strip()
        _require(observed_blob == entry["git_blob"], f"Git blob mismatch: {role}")
        raw = _git_bytes(repo_root, "cat-file", "blob", observed_blob)
        _require(sha256_bytes(raw) == entry["sha256"], f"Git blob SHA-256 mismatch: {role}")
    head_source_blob = _git_bytes(
        repo_root,
        "rev-parse",
        f"HEAD:{by_role[CURRENT_SOURCE_ROLE]['tracked_path']}",
    ).decode("ascii").strip()
    _require(
        head_source_blob == by_role[CURRENT_SOURCE_ROLE]["git_blob"],
        "current review source no longer matches the versioned current-source contract",
    )
    return by_role


def historical_review_binding_matches(
    binding: dict[str, Any],
    *,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = CONTRACT_PATH,
) -> bool:
    try:
        by_role = verify_contract(repo_root=repo_root, contract_path=contract_path)
        historical = by_role[FROZEN_REVIEW_ROLE]
        return (
            binding.get("path") == historical["tracked_path"]
            and binding.get("sha256") == historical["sha256"]
        )
    except (KeyError, OSError, PillarV1IdentityContractError, TypeError):
        return False


def bindings_match_declared_identities(
    bindings: Iterable[dict[str, Any]],
    *,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = CONTRACT_PATH,
) -> bool:
    """Check mixed V1 bindings without comparing historical pins to live bytes."""
    try:
        by_role = verify_contract(repo_root=repo_root, contract_path=contract_path)
        historical = by_role[FROZEN_REVIEW_ROLE]
        contract = qft_route_evidence_identity.load_contract()
        qft_paths = {entry["path"] for entry in contract["identities"]}
        bindings_list = list(bindings)
        if not qft_route_evidence_identity.bindings_match_declared_identities(
            [binding for binding in bindings_list if binding.get("path") in qft_paths],
            repo_root=repo_root,
        ):
            return False
        for binding in bindings_list:
            path = binding.get("path")
            expected_sha256 = binding.get("sha256")
            if path in qft_paths:
                continue
            if path == historical["tracked_path"]:
                if expected_sha256 != historical["sha256"]:
                    return False
                continue
            artifact_path = repo_root / path
            if (
                not artifact_path.is_file()
                or sha256_bytes(artifact_path.read_bytes()) != expected_sha256
            ):
                return False
    except (
        KeyError,
        OSError,
        PillarV1IdentityContractError,
        qft_route_evidence_identity.IdentityContractError,
        TypeError,
    ):
        return False
    return True
