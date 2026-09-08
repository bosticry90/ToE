from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
REGISTRY_PATH = RELEASE_DIR / "LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_PATH = RELEASE_DIR / "CURRENT_MAINTENANCE_AUTHORITY_v0.json"
SELECTOR_PATH = RELEASE_DIR / (
    "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_"
    "MAINTENANCE_ROUTE_SELECTION_20260719_v0.json"
)
PACKET_PATH = RELEASE_DIR / (
    "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_PACKET_20260719_v0.json"
)
REVIEW_PATH = RELEASE_DIR / (
    "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_"
    "AUTHORIZATION_INDEPENDENT_REVIEW_20260719_v0.json"
)

AUDITED_COMMIT = "75af1d110a57df26344ca151ccd26b9f5c1f7736"
PREVIOUS_MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
PREVIOUS_MAINTENANCE_EVIDENCE = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_"
    "GUARDRAIL_PACKET_20260711_v0.json"
)
PREVIOUS_MAINTENANCE_EVIDENCE_SHA256 = (
    "7371ff496fc8fd948e892e0136d380991c6f87128201d12fe7ff6f5df9ffa764"
)
MAINTENANCE_CONSUMER_INVENTORY = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_INVENTORY_20260711_v0.json"
)
MAINTENANCE_CONSUMER_INVENTORY_SHA256 = (
    "4dc376cedfafad55f950e62057113ab3f6695f28ad986a42e723fe451904aac4"
)
SELECTOR_ID = (
    "select_repository_authority_custody_and_reproducibility_"
    "recovery_maintenance_route_v0"
)
RECOVERY_TARGET = (
    "prepare_repository_authority_custody_and_reproducibility_recovery_packet_v0"
)
RECOVERY_AUTHORITY = (
    "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_PACKET_v0"
)
STABILIZATION_TARGET = (
    "prepare_repository_clean_baseline_validation_stabilization_packet_v0"
)


class AuthorizationError(RuntimeError):
    pass


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_bytes(value: dict[str, Any]) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _repo_path(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def _scientific_snapshot(registry: dict[str, Any]) -> dict[str, Any]:
    return {
        "source": _repo_path(REGISTRY_PATH),
        "source_sha256": _sha256_path(REGISTRY_PATH),
        "current_target": registry["CURRENT_LIVE_NEXT_TARGET_v0"],
        "current_target_kind": registry["CURRENT_LIVE_TARGET_KIND_v0"],
        "current_target_evidence": registry["CURRENT_LIVE_TARGET_EVIDENCE_v0"],
        "current_target_report": registry["CURRENT_LIVE_TARGET_REPORT_v0"],
        "current_target_outcome": registry["CURRENT_LIVE_TARGET_OUTCOME_v0"],
        "current_target_strict_outcome": registry[
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0"
        ],
        "posture": "B-BLOCKED",
        "resolved_unit_seam_rows": 0,
        "blocked_unit_seam_rows": 12,
        "blocked_seams": 5,
        "phase_2_authorized": False,
        "master_action_promoted": False,
        "empirical_validation_established": False,
    }


def build_selector() -> dict[str, Any]:
    registry = _read_json(REGISTRY_PATH)
    return {
        "schema_id": (
            "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_"
            "MAINTENANCE_ROUTE_SELECTION_20260719_v0"
        ),
        "status": "SELECTED_PENDING_INDEPENDENT_AUTHORIZATION_REVIEW",
        "audited_commit": AUDITED_COMMIT,
        "selected_route": SELECTOR_ID,
        "selected_maintenance_target": RECOVERY_TARGET,
        "previous_maintenance_target": PREVIOUS_MAINTENANCE_TARGET,
        "previous_maintenance_lane_disposition": "DEFERRED_NOT_RETIRED",
        "scientific_authority": _scientific_snapshot(registry),
        "boundaries": {
            "scientific_target_unchanged": True,
            "scientific_authority_unchanged": True,
            "scientific_execution_frozen": True,
            "scientific_registry_mutation_authorized": False,
            "v2_regeneration_authorized": False,
            "first_unit_selector_execution_authorized": False,
            "scalar_yukawa_execution_authorized": False,
            "maxwell_dirac_execution_authorized": False,
            "phase_2_authorized": False,
        },
    }


def build_packet(selector: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": (
            "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_"
            "PACKET_20260719_v0"
        ),
        "status": "PREPARED_PENDING_INDEPENDENT_AUTHORIZATION_REVIEW",
        "maintenance_authority": RECOVERY_AUTHORITY,
        "maintenance_target": RECOVERY_TARGET,
        "selector": {
            "path": _repo_path(SELECTOR_PATH),
            "sha256": _sha256_bytes(_canonical_bytes(selector)),
        },
        "audited_repository": {
            "path": "C:/Users/psboy/Documents/ToE",
            "commit": AUDITED_COMMIT,
            "evidence_only": True,
            "full_suite_rerun_authorized": False,
        },
        "phases": [
            {
                "phase": "A",
                "name": "READ_ONLY_EVIDENCE_ACQUISITION",
                "may_modify_audited_worktree": False,
                "successor_requires_independent_acceptance": True,
            },
            {
                "phase": "B",
                "name": "CONTROL_PLANE_AND_VALIDATION_REPAIR",
                "may_start_before_phase_a_acceptance": False,
                "scientific_status_changes_authorized": False,
            },
            {
                "phase": "C",
                "name": "CLEAN_REPRODUCIBILITY_AND_PROVENANCE_ADJUDICATION",
                "must_run_in_fresh_clone": True,
                "scientific_resumption_authorized_by_completion": False,
            },
        ],
        "frozen_scientific_authority": selector["scientific_authority"],
        "prohibitions": [
            "NO_SCIENTIFIC_TARGET_ROTATION",
            "NO_UNIT_OR_SEAM_ROW_CHANGE",
            "NO_ROUTE_MAP_ACCEPTANCE",
            "NO_MASTER_ACTION_PROMOTION",
            "NO_EMPIRICAL_CLAIM",
            "NO_V2_REGENERATION",
            "NO_FIRST_UNIT_SELECTOR_EXECUTION",
            "NO_SCALAR_YUKAWA_EXECUTION",
            "NO_MAXWELL_DIRAC_EXECUTION",
            "NO_STAGE_A_OR_STAGE_B_EXECUTION",
        ],
        "terminal_outcomes": [
            "RECOVERY_READY_FOR_GOVERNED_SCIENTIFIC_RESUMPTION",
            "RECOVERY_BLOCKED_CUSTODY_GAP",
            "RECOVERY_BLOCKED_AUTHORITY_PROVENANCE",
            "RECOVERY_BLOCKED_CLEAN_VALIDATION",
            "RECOVERY_BLOCKED_TOOLCHAIN_REPRODUCIBILITY",
        ],
    }


def build_maintenance_authority(packet: dict[str, Any]) -> dict[str, Any]:
    registry = _read_json(REGISTRY_PATH)
    previous = _read_json(MAINTENANCE_PATH)
    if previous.get("current_maintenance_target") not in {
        PREVIOUS_MAINTENANCE_TARGET,
        RECOVERY_TARGET,
        STABILIZATION_TARGET,
    }:
        raise AuthorizationError("unexpected prior maintenance target")
    historical_snapshot = previous.get(
        "historical_scientific_snapshot", previous["scientific_authority"]
    )
    return {
        "schema_id": "CURRENT_MAINTENANCE_AUTHORITY_v0",
        "status": "ACTIVE_OPERATIONAL_NONSCIENTIFIC_RECOVERY_AUTHORITY",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "current_maintenance_target": RECOVERY_TARGET,
        "current_maintenance_target_kind": "repository_authority_custody_recovery",
        "current_maintenance_target_status": "AUTHORIZED_PHASE_A_ONLY",
        "current_maintenance_target_evidence": _repo_path(PACKET_PATH),
        "current_maintenance_target_evidence_sha256": _sha256_bytes(
            _canonical_bytes(packet)
        ),
        "previous_maintenance_target": PREVIOUS_MAINTENANCE_TARGET,
        "previous_maintenance_lane_disposition": "DEFERRED_NOT_RETIRED",
        "previous_maintenance_target_evidence": PREVIOUS_MAINTENANCE_EVIDENCE,
        "previous_maintenance_target_evidence_sha256": (
            PREVIOUS_MAINTENANCE_EVIDENCE_SHA256
        ),
        "maintenance_program_source": previous["maintenance_program_source"],
        "maintenance_program_source_sha256": previous[
            "maintenance_program_source_sha256"
        ],
        "maintenance_consumer_inventory_path": MAINTENANCE_CONSUMER_INVENTORY,
        "maintenance_consumer_inventory_sha256": (
            MAINTENANCE_CONSUMER_INVENTORY_SHA256
        ),
        "historical_scientific_snapshot": historical_snapshot,
        "scientific_authority": _scientific_snapshot(registry),
        "boundary": {
            "scientific_target_displaced": False,
            "scientific_target_rotated": False,
            "scientific_execution_authorized": False,
            "phase_b_authorized": False,
            "phase_c_authorized": False,
            "registry_sharding_migration_authorized": False,
            "v2_regeneration_authorized": False,
            "first_unit_selector_execution_authorized": False,
        },
    }


def _write(path: Path, value: dict[str, Any]) -> None:
    path.write_bytes(_canonical_bytes(value))


def prepare(*, write: bool) -> tuple[dict[str, Any], dict[str, Any]]:
    selector = build_selector()
    packet = build_packet(selector)
    if write:
        _write(SELECTOR_PATH, selector)
        _write(PACKET_PATH, packet)
    else:
        if SELECTOR_PATH.read_bytes() != _canonical_bytes(selector):
            raise AuthorizationError("maintenance route selector is stale")
        if PACKET_PATH.read_bytes() != _canonical_bytes(packet):
            raise AuthorizationError("recovery packet is stale")
    return selector, packet


def activate() -> None:
    _, packet = prepare(write=False)
    review = _read_json(REVIEW_PATH)
    if review.get("verdict") != "ACCEPT" or review.get("accepted") is not True:
        raise AuthorizationError("independent authorization review is not accepted")
    if review.get("packet_sha256") != _sha256_path(PACKET_PATH):
        raise AuthorizationError("review does not bind the recovery packet")
    _write(MAINTENANCE_PATH, build_maintenance_authority(packet))


def check_activated() -> None:
    _, packet = prepare(write=False)
    expected = _canonical_bytes(build_maintenance_authority(packet))
    if MAINTENANCE_PATH.read_bytes() != expected:
        raise AuthorizationError("current maintenance authority is not activated")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--activate", action="store_true")
    args = parser.parse_args()
    if args.write:
        prepare(write=True)
    elif args.activate:
        activate()
    else:
        check_activated()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
