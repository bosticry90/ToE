from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
ARCHITECTURE_SCHEMA_PATH = REPO_ROOT / "ARCHITECTURE_SCHEMA_v1.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_text(_read(path))


def _lock_path_and_version() -> tuple[Path, int]:
    lock_paths = sorted(REPO_ROOT.glob("GOVERNANCE_VERSION_v*.lock"))
    assert lock_paths, "Missing governance lock file (expected GOVERNANCE_VERSION_v*.lock)."

    versioned: list[tuple[int, Path]] = []
    for path in lock_paths:
        m = re.fullmatch(r"GOVERNANCE_VERSION_v(\d+)\.lock", path.name)
        assert m is not None, f"Invalid governance lock filename: {path.name}"
        versioned.append((int(m.group(1)), path))

    versioned.sort()
    return versioned[-1][1], versioned[-1][0]


def _adjudication_class_list(schema: dict) -> list[str]:
    classes = list(schema.get("allowed_adjudication_prefixes", []))
    classes.extend(schema.get("legacy_allowed_adjudication_prefixes", []))
    return sorted(set(classes))


def test_governance_tracked_surface_changes_require_explicit_versioned_lock_sync() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    lock_path, lock_version = _lock_path_and_version()
    lock = _read_json(lock_path)

    assert lock.get("governance_version") == lock_version, (
        f"{lock_path.name}: governance_version must match filename version v{lock_version}."
    )
    assert int(schema.get("schema_version", 0)) == lock_version, (
        "ARCHITECTURE_SCHEMA_v1.json schema_version must match latest governance lock version. "
        "If governance structure changed, bump schema/lock version together."
    )

    tracked_hashes: dict[str, str] = lock.get("tracked_hashes", {})
    required_tracked = [
        "ARCHITECTURE_SCHEMA_v1.json",
        "formal/docs/paper/ASSUMPTION_REGISTRY_v1.md",
    ]
    missing_keys = [key for key in required_tracked if key not in tracked_hashes]
    assert not missing_keys, f"{lock_path.name} is missing tracked hash key(s): {', '.join(missing_keys)}"

    hash_violations: list[str] = []
    for rel_path, expected_hash in sorted(tracked_hashes.items()):
        target = REPO_ROOT / rel_path
        assert target.exists(), f"{lock_path.name} references missing tracked file: {rel_path}"
        observed_hash = _sha256_file(target)
        if observed_hash != expected_hash:
            hash_violations.append(f"{rel_path}: expected={expected_hash}, observed={observed_hash}")

    expected_adjudication_list = _adjudication_class_list(schema)
    observed_adjudication_list = lock.get("adjudication_class_list", [])
    assert observed_adjudication_list == expected_adjudication_list, (
        "Adjudication class list drift detected between architecture schema and governance lock. "
        "Bump governance version and regenerate lock."
    )

    adjudication_digest = _sha256_text(json.dumps(expected_adjudication_list, separators=(",", ":")))
    assert lock.get("adjudication_class_list_sha256") == adjudication_digest, (
        "Adjudication class list digest drift detected. Bump governance version and regenerate lock."
    )

    assert not hash_violations, (
        "Governance tracked surface changed without synchronized versioned lock. "
        "Bump governance version and add/update GOVERNANCE_VERSION_v*.lock.\n- "
        + "\n- ".join(hash_violations)
    )
