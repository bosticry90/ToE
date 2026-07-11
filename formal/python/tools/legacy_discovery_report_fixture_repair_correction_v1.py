from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "205f19ce0f502c1bb19c5f3d116dcf18506e7b92"
V0_PATH = (
    "formal/docs/release/"
    "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v0.json"
)
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v1.json"
)
EXPECTED_V0_SHA256 = "e70d8741de6378e4f00bb135607cb92b06ad83ee8b78e0675b93a6226720f9eb"
SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)


class CorrectionError(ValueError):
    pass


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _git_blob(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise CorrectionError(f"missing committed repair source: {relative}")
    return result.stdout


def _committed_row(relative: str, role: str) -> dict[str, Any]:
    raw = _git_blob(relative)
    return {
        "hash_policy": "EXACT_COMMITTED_GIT_BLOB_BYTES",
        "path": relative,
        "role": role,
        "sha256": _sha256(raw),
        "size_bytes": len(raw),
    }


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def build_correction() -> dict[str, Any]:
    v0_raw = _git_blob(V0_PATH)
    if _sha256(v0_raw) != EXPECTED_V0_SHA256:
        raise CorrectionError("immutable v0 repair artifact hash mismatch")
    v0 = json.loads(v0_raw)
    if v0["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise CorrectionError("scientific target drift in v0 repair")
    if v0["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise CorrectionError("maintenance target drift in v0 repair")

    fixture_rows = []
    for row in v0["root_fixtures"]:
        raw = _git_blob(row["path"])
        if len(raw) != row["size_bytes"] or _sha256(raw) != row["sha256"]:
            raise CorrectionError(f"committed root fixture mismatch: {row['path']}")
        fixture_rows.append(
            {
                **row,
                "hash_policy": "EXACT_COMMITTED_GIT_BLOB_BYTES_NO_TEXT_NORMALIZATION",
            }
        )

    implementation_files = [
        _committed_row(
            "formal/python/tests/legacy_discovery_report_fixture_materializer.py",
            "session materializer",
        ),
        _committed_row(
            "formal/python/tests/conftest.py",
            "pytest activation integration",
        ),
        _committed_row(
            "formal/python/tests/test_legacy_discovery_report_fixture_materializer.py",
            "materializer controls",
        ),
        _committed_row(
            "formal/python/tests/test_legacy_discovery_report_fixture_packet.py",
            "historical preparation-boundary assertion stabilization",
        ),
    ]

    old_conftest = next(
        row for row in v0["implementation_files"] if row["path"].endswith("conftest.py")
    )
    new_conftest = next(
        row for row in implementation_files if row["path"].endswith("conftest.py")
    )
    if old_conftest["sha256"] == new_conftest["sha256"]:
        raise CorrectionError("expected checkout-sensitive conftest binding was not corrected")

    return {
        "authorization": {
            "maintenance_target": MAINTENANCE_TARGET,
            "registry_migration_execution_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "source_repair_commit": SOURCE_COMMIT,
        },
        "boundary": {
            "fixture_bytes_changed": False,
            "fixture_logic_changed": False,
            "maintenance_target_rotated": False,
            "registry_migration_executed": False,
            "scientific_artifacts_modified": False,
            "scientific_claim_or_blocker_movement": False,
            "scientific_target_rotated": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "correction": {
            "corrected_field_class": "IMPLEMENTATION_SOURCE_IDENTITY_BINDING",
            "corrected_path": "formal/python/tests/conftest.py",
            "new_committed_sha256": new_conftest["sha256"],
            "new_committed_size_bytes": new_conftest["size_bytes"],
            "old_worktree_sha256": old_conftest["sha256"],
            "old_worktree_size_bytes": old_conftest["size_bytes"],
            "reason": "V0_BOUND_MIXED_EOL_WORKTREE_BYTES_INSTEAD_OF_COMMITTED_GIT_BYTES",
        },
        "implementation": v0["implementation"],
        "implementation_files": implementation_files,
        "repair_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v1",
        "root_fixtures": fixture_rows,
        "schema_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v1",
        "status": "VERSIONED_SOURCE_BINDING_CORRECTION_REPAIR_SCOPE_UNCHANGED_PENDING_RAW_DETACHED_CLEAN_CHECKOUT_ACCEPTANCE",
        "supersedes_v0_sha256": EXPECTED_V0_SHA256,
        "validation": {
            "first_raw_detached_run_pass_count": 189,
            "first_raw_detached_run_source_binding_failure_count": 1,
            "fixture_chain_failure_count": 0,
            "raw_detached_clean_checkout_full_manifest_passed": False,
            "raw_detached_clean_checkout_validation_pending": True,
            "runtime_paths_absent_after_failed_acceptance_run": 21,
        },
    }


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or verify the v1 fixture-repair evidence correction.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_correction())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise CorrectionError("legacy discovery fixture repair v1 correction mismatch")
        print(f"legacy_discovery_fixture_repair_correction_v1: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"legacy_discovery_fixture_repair_correction_v1: wrote {OUTPUT_PATH} sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
