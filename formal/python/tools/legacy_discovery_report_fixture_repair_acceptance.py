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
SOURCE_COMMIT = "153b183101086e1933a92260743a1cdf91b28498"
CORRECTION_PATH = (
    "formal/docs/release/"
    "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v1.json"
)
MANIFEST_PATH = "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_ACCEPTANCE_20260711_v0.json"
)
EXPECTED_CORRECTION_SHA256 = (
    "7befc5fd9500d2e099a26013eed159a6ece9dff1a3c29365a6c53314cd19b940"
)
SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)


class AcceptanceError(ValueError):
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
        raise AcceptanceError(f"missing acceptance source blob: {relative}")
    return result.stdout


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def build_acceptance() -> dict[str, Any]:
    correction_raw = _git_blob(CORRECTION_PATH)
    if _sha256(correction_raw) != EXPECTED_CORRECTION_SHA256:
        raise AcceptanceError("effective repair correction hash mismatch")
    correction = json.loads(correction_raw)
    manifest = json.loads(_git_blob(MANIFEST_PATH))
    critical = manifest["groups"]["critical_gates"]
    integrity = manifest["groups"]["integrity_gates"]
    combined_paths = list(dict.fromkeys(critical["tests"] + integrity["tests"]))
    if len(combined_paths) != 59:
        raise AcceptanceError("raw-clean manifest path-union count drift")
    if correction["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise AcceptanceError("scientific target drift")
    if correction["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise AcceptanceError("maintenance target drift")

    return {
        "acceptance_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_ACCEPTANCE_20260711_v0",
        "authorization": {
            "maintenance_target": MAINTENANCE_TARGET,
            "next_bounded_action": "prepare_corrective_loop_control_registry_sharding_guardrail_v1",
            "registry_migration_execution_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "source_commit": SOURCE_COMMIT,
        },
        "boundary": {
            "full_python_aggregate_claimed_green": False,
            "maintenance_target_rotated": False,
            "registry_migration_executed": False,
            "scientific_artifacts_modified": False,
            "scientific_claim_or_blocker_movement": False,
            "scientific_target_rotated": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "effective_repair_correction_sha256": EXPECTED_CORRECTION_SHA256,
        "raw_detached_clean_checkout": {
            "combined_manifest_path_count": len(combined_paths),
            "critical_group_expected_count": critical["expected_count"],
            "critical_group_expected_sha256": critical["expected_sha256"],
            "detached_worktree_git_clean_after": True,
            "detached_worktree_git_clean_before": True,
            "initial_runtime_path_absent_count": 21,
            "integrity_group_expected_count": integrity["expected_count"],
            "integrity_group_expected_sha256": integrity["expected_sha256"],
            "passed_test_count": 195,
            "runtime_path_count": 21,
            "teardown_runtime_path_absent_count": 21,
            "validation_result": "PASS",
        },
        "root_fixture_custody": [
            {
                "path": row["path"],
                "sha256": row["sha256"],
                "size_bytes": row["size_bytes"],
            }
            for row in correction["root_fixtures"]
        ],
        "schema_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_ACCEPTANCE_20260711_v0",
        "status": "ACCEPTED_FOCUSED_RAW_CLEAN_CHECKOUT_REPRODUCIBILITY_FULL_PYTHON_AGGREGATE_TIMEOUT_NOT_UPGRADED",
        "validation_ceiling": {
            "full_python_aggregate_elapsed_timeout_seconds": 1800,
            "full_python_aggregate_failed": False,
            "full_python_aggregate_passed": False,
            "full_python_aggregate_timed_out": True,
            "timeout_observed_phase": "LEAN_BUILD_TOEFORMAL_QFT_EVOLUTION_OBJECTSCAFFOLD",
            "timeout_process_tree_terminated": True,
            "timeout_runtime_outputs_removed_after_exact_path_and_hash_inspection": True,
            "wording": "focused raw-clean acceptance passed; full Python aggregate timed out and is not described as green",
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
    parser = argparse.ArgumentParser(description="Build or verify raw-clean fixture repair acceptance.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_acceptance())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise AcceptanceError("legacy discovery fixture repair acceptance mismatch")
        print(f"legacy_discovery_fixture_repair_acceptance: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"legacy_discovery_fixture_repair_acceptance: wrote {OUTPUT_PATH} sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
