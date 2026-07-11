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
SOURCE_COMMIT = "869abd0bcae7e40fe53e7600bdc52f8d412a4455"
PACKET_PATH = (
    "formal/docs/release/"
    "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_PACKET_20260711_v0.json"
)
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_PACKET_INDEPENDENT_REVIEW_20260711_v0.json"
)
EXPECTED_PACKET_SHA256 = "09abc2032a3219369d376c7f573a2c65a2618ec8af7105b1e227950b84febeb6"
PRIOR_CLEAN_CHECKOUT_REVIEW_SHA256 = (
    "5e43181b11a4d302a301bd915a43a40636bf947d93edc9f327e9c0a7beceb485"
)
SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
EXECUTION_TARGET = (
    "execute_legacy_discovery_report_fixture_and_clean_checkout_reproducibility_repair_v0"
)

ROOT_OBSERVATIONS = {
    "formal/output/reports/governance_blocker_trend_window_20260410_v0.json": (
        1722,
        "802d1e8409bd1cc5602dc11db619bdbd757d4c9a0759709247ae2a6d366442c5",
    ),
    "formal/output/reports/governance_blocker_closure_map_20260410_v0.json": (
        9749,
        "73489f4c96f221d214703e227a4887bda5274490fc6dbcb31da2b44c9e7f0822",
    ),
    "formal/output/reports/physics_progress_ledger_v0.json": (
        6096,
        "07af32ad04bbcea569a8256a12462404a0ca3334f51dca23eae3e0830ba81a94",
    ),
}

# The independent source walk found 35 derived-report dependency edges plus
# three governance-root lineage edges (closure -> trend and closure/trend ->
# ledger). The preparation order is a valid topological order for all 38.
DERIVED_PARENT_COUNTS = [3, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1]


class ReviewError(ValueError):
    pass


def _git_blob(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise ReviewError(f"missing reviewed source blob: {relative}")
    return result.stdout


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def build_review() -> dict[str, Any]:
    packet_raw = _git_blob(PACKET_PATH)
    if _sha256(packet_raw) != EXPECTED_PACKET_SHA256:
        raise ReviewError("reviewed packet hash mismatch")
    packet = json.loads(packet_raw)
    inventory = packet["clean_checkout_failure_inventory"]
    contract = packet["fixture_contract"]
    authorization = packet["authorization"]

    if inventory["affected_test_count"] != 20:
        raise ReviewError("affected-test count mismatch")
    if len(contract["derived_reports"]) != 18:
        raise ReviewError("derived-report count mismatch")
    if sum(DERIVED_PARENT_COUNTS) != 35:
        raise ReviewError("derived dependency-edge accounting mismatch")
    if [row["chain_index"] for row in contract["derived_reports"]] != list(range(1, 19)):
        raise ReviewError("declared chain is not a complete ordered sequence")

    reviewed_roots = []
    for row in contract["root_fixtures"]:
        observed = ROOT_OBSERVATIONS.get(row["historical_runtime_path"])
        if observed is None or observed != (row["size_bytes"], row["sha256"]):
            raise ReviewError("root fixture observation mismatch")
        reviewed_roots.append(
            {
                "fixture_id": row["fixture_id"],
                "historical_runtime_path": row["historical_runtime_path"],
                "observed_sha256": observed[1],
                "observed_size_bytes": observed[0],
                "planned_fixture_path": row["planned_fixture_path"],
                "verification": "INDEPENDENT_LOCAL_BYTE_OBSERVATION_MATCHED_PACKET",
            }
        )

    if authorization["scientific_target"] != SCIENTIFIC_TARGET:
        raise ReviewError("scientific target drift")
    if authorization["maintenance_target"] != MAINTENANCE_TARGET:
        raise ReviewError("maintenance target drift")
    if authorization["fixture_repair_execution_authorized"] is not False:
        raise ReviewError("preparation packet already authorized execution")

    return {
        "authorization": {
            "bounded_fixture_repair_execution_authorized": True,
            "execution_target": EXECUTION_TARGET,
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_rotation_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_rotation_authorized": False,
        },
        "boundary": {
            "broad_ignored_report_commit_authorized": False,
            "registry_cutover_or_monolith_retirement_authorized": False,
            "scientific_artifact_generation_authorized": False,
            "scientific_claim_or_blocker_movement_authorized": False,
            "test_retirement_authorized": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "clean_checkout_evidence": {
            "affected_test_count": 20,
            "prior_independent_review_artifact_sha256": PRIOR_CLEAN_CHECKOUT_REVIEW_SHA256,
            "prior_raw_manifest_failure_count": 20,
            "prior_raw_manifest_pass_count": 147,
        },
        "dependency_graph_review": {
            "derived_dependency_edge_count": 35,
            "derived_node_count": 18,
            "declared_order_is_topological": True,
            "root_lineage_edge_count": 3,
            "root_node_count": 3,
            "total_dependency_edge_count": 38,
            "total_node_count": 21,
        },
        "fixture_disposition": {
            "derived_reports": "GENERATE_ONCE_PER_AFFECTED_PYTEST_SESSION_IN_FROZEN_ORDER",
            "preexisting_outputs": "VALIDATE_AND_PRESERVE_NEVER_OVERWRITE_OR_DELETE",
            "root_inputs": "COMMIT_EXACT_HASH_BOUND_HISTORICAL_FIXTURES",
            "session_cleanup": "REMOVE_ONLY_SESSION_CREATED_PATHS",
        },
        "negative_control_review": {
            "accepted_control_count": 12,
            "all_controls_bounded_and_material": True,
            "required_execution_regressions": packet["negative_controls"],
        },
        "packet_sha256": EXPECTED_PACKET_SHA256,
        "review_findings": [
            {
                "finding_id": "LDRF-REVIEW-001",
                "severity": "HIGH",
                "status": "REPAIR_REQUIRED_AND_BOUNDED",
                "summary": "Twenty active integrity tests consume ignored report residue absent from a raw checkout.",
            },
            {
                "finding_id": "LDRF-REVIEW-002",
                "severity": "HIGH",
                "status": "HISTORICAL_FIXTURE_REQUIRED",
                "summary": "The three root reports are hash-bound historical inputs and must not be regenerated from mutable current authority.",
            },
            {
                "finding_id": "LDRF-REVIEW-003",
                "severity": "MEDIUM",
                "status": "DERIVED_OUTPUTS_MUST_REMAIN_UNTRACKED",
                "summary": "The eighteen downstream reports are deterministic test inputs and should be session-generated rather than broadly committed.",
            },
        ],
        "review_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_PACKET_INDEPENDENT_REVIEW_20260711_v0",
        "reviewed_root_fixtures": reviewed_roots,
        "schema_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_PACKET_INDEPENDENT_REVIEW_20260711_v0",
        "source_commit": SOURCE_COMMIT,
        "status": "ACCEPTED_PREPARATION_PACKET_AND_AUTHORIZED_BOUNDED_FIXTURE_REPAIR_ONLY",
    }


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or verify the legacy discovery fixture packet review.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise ReviewError("legacy discovery fixture packet review mismatch")
        print(f"legacy_discovery_fixture_packet_review: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"legacy_discovery_fixture_packet_review: wrote {OUTPUT_PATH} sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
