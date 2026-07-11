from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests import legacy_discovery_report_fixture_materializer as materializer
from formal.python.tools.legacy_discovery_report_fixture_packet import ROOT_FIXTURES


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_REVIEW_COMMIT = "225f6d3a706364fbf51de372d38189e1d46af766"
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v0.json"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal/docs/release/LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_PACKET_INDEPENDENT_REVIEW_20260711_v0.json"
)
EXPECTED_REVIEW_SHA256 = "cc38957def8b67d033f89b74496f95ef759cc0a871405673b899102bfbdcf6b0"
SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)


class RepairArtifactError(ValueError):
    pass


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _file_row(relative: str, role: str) -> dict[str, Any]:
    raw = (REPO_ROOT / relative).read_bytes()
    return {
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


def build_artifact() -> dict[str, Any]:
    materializer.validate_contract()
    if _sha256(REVIEW_PATH.read_bytes()) != EXPECTED_REVIEW_SHA256:
        raise RepairArtifactError("authorizing review hash mismatch")
    fixture_rows = []
    for row in ROOT_FIXTURES:
        relative = row["planned_fixture_path"]
        raw = (REPO_ROOT / relative).read_bytes()
        materializer._validate_root_fixture(raw, row)
        fixture_rows.append(
            {
                "fixture_id": row["fixture_id"],
                "path": relative,
                "sha256": _sha256(raw),
                "size_bytes": len(raw),
                "historical_runtime_path": row["historical_runtime_path"],
            }
        )

    return {
        "authorization": {
            "authorizing_review_sha256": EXPECTED_REVIEW_SHA256,
            "maintenance_target": MAINTENANCE_TARGET,
            "registry_migration_execution_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "source_review_commit": SOURCE_REVIEW_COMMIT,
        },
        "boundary": {
            "broad_ignored_report_commit_performed": False,
            "maintenance_target_rotated": False,
            "registry_migration_executed": False,
            "scientific_artifacts_modified": False,
            "scientific_claim_or_blocker_movement": False,
            "scientific_target_rotated": False,
            "test_retirement_performed": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "implementation": {
            "affected_test_count": 20,
            "canonical_derived_encoding": "UTF-8_NO_BOM_LF_TERMINAL_NEWLINE_SORTED_KEYS_FINITE_JSON",
            "derived_dependency_edge_count": sum(
                len(rows) for rows in materializer.DERIVED_DEPENDENCIES.values()
            ),
            "derived_report_count": 18,
            "fixture_activation": "EXACT_AFFECTED_TEST_COLLECTION_ONLY",
            "fixture_cleanup": "LOCK_HELD_REMOVE_ONLY_SESSION_CREATED_UNCHANGED_PATHS",
            "preexisting_policy": "VALIDATE_AND_PRESERVE_NEVER_OVERWRITE_OR_DELETE",
            "report_node_count": 21,
            "root_fixture_count": 3,
            "root_lineage_edge_count": 3,
        },
        "implementation_files": [
            _file_row(
                "formal/python/tests/legacy_discovery_report_fixture_materializer.py",
                "session materializer",
            ),
            _file_row("formal/python/tests/conftest.py", "pytest activation integration"),
            _file_row(
                "formal/python/tests/test_legacy_discovery_report_fixture_materializer.py",
                "materializer controls",
            ),
            _file_row(
                "formal/python/tests/test_legacy_discovery_report_fixture_packet.py",
                "historical preparation-boundary assertion stabilization",
            ),
        ],
        "negative_control_disposition": {
            "contract_control_count": 12,
            "implemented_classes": [
                "missing_root_fixture_rejected",
                "root_fixture_hash_mismatch_rejected",
                "root_fixture_size_mismatch_rejected",
                "duplicate_runtime_output_rejected",
                "producer_chain_cycle_rejected",
                "producer_order_violation_rejected",
                "unclassified_failing_test_rejected",
                "preexisting_runtime_report_never_overwritten",
                "cleanup_removes_only_session_created_paths",
                "fixture_activation_skipped_when_no_affected_test_selected",
                "generated_report_bytes_deterministic_across_two_runs",
            ],
            "pending_external_acceptance_control": "raw_clean_checkout_full_manifest_required",
        },
        "repair_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v0",
        "root_fixtures": fixture_rows,
        "schema_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v0",
        "status": "BOUNDED_FIXTURE_REPAIR_IMPLEMENTED_PENDING_RAW_DETACHED_CLEAN_CHECKOUT_ACCEPTANCE",
        "validation": {
            "affected_and_materializer_focused_pass_count": 27,
            "focused_validation_passed": True,
            "raw_detached_clean_checkout_full_manifest_passed": False,
            "raw_detached_clean_checkout_validation_pending": True,
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
    parser = argparse.ArgumentParser(description="Build or verify the legacy discovery fixture repair artifact.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_artifact())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise RepairArtifactError("legacy discovery fixture repair artifact mismatch")
        print(f"legacy_discovery_fixture_repair: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"legacy_discovery_fixture_repair: wrote {OUTPUT_PATH} sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
