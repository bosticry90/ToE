from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    july_16_19_repository_integration_and_live_authority_repair_maintenance_packet_review_v0
    as review,
)


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_V0_PATH = (
    REPO_ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
)
AUTHORITY_PATH = (
    REPO_ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v1.json"
)
POINTER_PATH = (
    REPO_ROOT
    / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0.json"
)

SCIENTIFIC_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)
MAINTENANCE_TARGET = (
    "execute_july_16_19_repository_integration_and_live_authority_repair_v0"
)
RESULT_REVIEW_TARGET = (
    "review_july_16_19_repository_integration_and_live_authority_"
    "repair_execution_result_v0"
)
REVIEW_COMMIT = "4d992c9ceaf4ca2ea961abf908295ba86653fc4f"
REVIEW_SHA256 = (
    "f0795033e96f6628ec27affd38f4266bd048bb4ae3e5c002e487f776bb256fdd"
)
MAINTENANCE_V0_SHA256 = (
    "1d6604e25da32a886d1431c6eb3a92c16e4082d8b9ac5cda8bc16a469e99d224"
)


class CurrentMaintenanceAuthorityError(RuntimeError):
    pass


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise CurrentMaintenanceAuthorityError(f"expected JSON object: {path}")
    return value


def _canonical_bytes(value: dict[str, Any]) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _registry_projection(registry: dict[str, Any]) -> dict[str, Any]:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise CurrentMaintenanceAuthorityError("registry current projection missing")
    return projection


def build_authority() -> dict[str, Any]:
    registry = _read_json(REGISTRY_PATH)
    projection = _registry_projection(registry)
    maintenance_v0 = _read_json(MAINTENANCE_V0_PATH)
    reviewed = json.loads(review.artifact_bytes().decode("utf-8"))

    if projection.get("current_target") != SCIENTIFIC_TARGET:
        raise CurrentMaintenanceAuthorityError("scientific target drift")
    if _sha256(MAINTENANCE_V0_PATH) != MAINTENANCE_V0_SHA256:
        raise CurrentMaintenanceAuthorityError("maintenance-v0 custody drift")
    if _sha256(review.REPORT_PATH) != REVIEW_SHA256:
        raise CurrentMaintenanceAuthorityError("maintenance review custody drift")
    if reviewed.get("selected_next_target") != MAINTENANCE_TARGET:
        raise CurrentMaintenanceAuthorityError("review did not authorize execution")
    if not reviewed["authorization"]["bounded_integration_execution_authorized"]:
        raise CurrentMaintenanceAuthorityError("integration execution is not authorized")
    if reviewed["scientific_firewall"]["scientific_target_rotation_authorized"]:
        raise CurrentMaintenanceAuthorityError("review unexpectedly rotates science")

    return {
        "schema_id": "CURRENT_MAINTENANCE_AUTHORITY_v1",
        "captured_at_utc": "2026-07-27T00:00:00Z",
        "status": (
            "ACTIVE_OPERATIONAL_NONSCIENTIFIC_REPOSITORY_INTEGRATION_"
            "EXECUTION_ONLY"
        ),
        "current_maintenance_target": MAINTENANCE_TARGET,
        "current_maintenance_target_kind": (
            "repository_integration_and_live_authority_repair_execution"
        ),
        "current_maintenance_target_status": (
            "AUTHORIZED_BY_INDEPENDENT_MAINTENANCE_PACKET_REVIEW"
        ),
        "current_maintenance_target_evidence": review.REPORT_PATH.relative_to(
            REPO_ROOT
        ).as_posix(),
        "current_maintenance_target_evidence_sha256": REVIEW_SHA256,
        "current_maintenance_target_evidence_commit": REVIEW_COMMIT,
        "required_result_review_target": RESULT_REVIEW_TARGET,
        "previous_maintenance_authority": {
            "path": MAINTENANCE_V0_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": MAINTENANCE_V0_SHA256,
            "target": maintenance_v0["current_maintenance_target"],
            "status": "SUPERSEDED_AS_CURRENT_RETAINED_IMMUTABLE_HISTORY",
        },
        "scientific_authority": {
            "source": REGISTRY_PATH.relative_to(REPO_ROOT).as_posix(),
            "source_sha256": _sha256(REGISTRY_PATH),
            "current_target": projection["current_target"],
            "previous_target": projection["previous_target"],
            "target_rotated": False,
        },
        "authorized_scope": reviewed["authorization"],
        "boundary": {
            "maintenance_target_inserted_into_scientific_workstreams": False,
            "scientific_target_displaced": False,
            "scientific_target_rotated": False,
            "july_16_19_scientific_chain_adopted": False,
            "new_physics_authorized": False,
            "yukawa_execution_or_rerun_authorized": False,
            "pipe_repair_and_rerun_authorized": False,
            "preserved_observations_validation_use_authorized": False,
            "terminal_yukawa_selection_authorized": False,
            "production_change_authorized": False,
            "integration_result_review_required": True,
            "post_maintenance_scientific_reconciliation_required": True,
        },
    }


def authority_bytes() -> bytes:
    return _canonical_bytes(build_authority())


def build_pointer(authority_data: bytes) -> dict[str, Any]:
    return {
        "schema_id": "CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0",
        "captured_at_utc": "2026-07-27T00:00:00Z",
        "current_authority_path": AUTHORITY_PATH.relative_to(REPO_ROOT).as_posix(),
        "current_authority_sha256": _sha256_bytes(authority_data),
        "current_authority_schema_id": "CURRENT_MAINTENANCE_AUTHORITY_v1",
        "current_maintenance_target": MAINTENANCE_TARGET,
        "scientific_target": SCIENTIFIC_TARGET,
        "authority_rule": (
            "Resolve the current operational maintenance authority through this "
            "pointer. Historical versioned authority files remain immutable and "
            "do not override the pointed current authority."
        ),
    }


def pointer_bytes(authority_data: bytes | None = None) -> bytes:
    data = authority_data if authority_data is not None else authority_bytes()
    return _canonical_bytes(build_pointer(data))


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate current maintenance authority v1 and its pointer."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()

    expected_authority = authority_bytes()
    expected_pointer = pointer_bytes(expected_authority)
    current_authority = AUTHORITY_PATH.read_bytes() if AUTHORITY_PATH.exists() else None
    current_pointer = POINTER_PATH.read_bytes() if POINTER_PATH.exists() else None

    if args.write:
        if current_authority != expected_authority:
            AUTHORITY_PATH.write_bytes(expected_authority)
            print(f"wrote {AUTHORITY_PATH.relative_to(REPO_ROOT).as_posix()}")
        if current_pointer != expected_pointer:
            POINTER_PATH.write_bytes(expected_pointer)
            print(f"wrote {POINTER_PATH.relative_to(REPO_ROOT).as_posix()}")
        return 0
    if current_authority != expected_authority:
        print("current maintenance authority v1 drift")
        return 1
    if current_pointer != expected_pointer:
        print("current maintenance authority pointer drift")
        return 1
    print(f"current maintenance authority v1 OK target={MAINTENANCE_TARGET}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
