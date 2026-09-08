from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_V0_PATH = (
    REPO_ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
)
BASELINE_REVIEW_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "CLEAN_INTEGRATION_CANDIDATE_RESULT_REVIEW_20260725_v0.json"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "JULY_16_19_REPOSITORY_INTEGRATION_AND_LIVE_AUTHORITY_REPAIR_"
    "MAINTENANCE_PACKET_20260727_v0.json"
)

SCIENTIFIC_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)
CONSUMED_MAINTENANCE_TARGET = (
    "preserve_accepted_post_pillar_historical_artifact_currency_role_"
    "separation_repair_baseline_reassessment_v0"
)
PACKET_TARGET = (
    "prepare_july_16_19_repository_integration_and_live_authority_"
    "repair_maintenance_packet_v0"
)
SELECTED_NEXT_TARGET = (
    "review_july_16_19_repository_integration_and_live_authority_"
    "repair_maintenance_packet_v0_result"
)
OBSERVED_LEAN_TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_exploratory_"
    "sandbox_v1_execution_result_review_scientific_response_v0"
)

CUSTODY_MANIFEST_SHA256 = (
    "5ef2a369f40e37b41d6bad5dc1e1f442bc0f8344811386fdf27acadfc5c4ae39"
)
CUSTODY_ARCHIVE_SHA256 = (
    "83c634813cad11de1a8d0389ef9de32526c291b609d498d8c7d6118becfa2902"
)
CUSTODY_BASE_COMMIT = "75af1d110a57df26344ca151ccd26b9f5c1f7736"
RESTRUCTURED_BASELINE_COMMIT = "a099c6867493d48a7aaba2f79bf2e29ecbf2cfd3"
SOURCE_INTEGRATION_TIP = "5aeb74ae46db2c397da40be0286287a5a63d5642"


class MaintenancePacketError(RuntimeError):
    pass


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise MaintenancePacketError(f"expected JSON object: {path}")
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _registry_target(registry: dict[str, Any]) -> str:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise MaintenancePacketError("registry current_projection_v0 is missing")
    target = projection.get("current_target")
    if not isinstance(target, str) or not target:
        raise MaintenancePacketError("registry scientific target is missing")
    return target


def build_packet() -> dict[str, Any]:
    registry = _read_json(REGISTRY_PATH)
    maintenance = _read_json(MAINTENANCE_V0_PATH)
    baseline_review = _read_json(BASELINE_REVIEW_PATH)

    registry_target = _registry_target(registry)
    if registry_target != SCIENTIFIC_TARGET:
        raise MaintenancePacketError("canonical scientific target drift")
    if maintenance.get("current_maintenance_target") != CONSUMED_MAINTENANCE_TARGET:
        raise MaintenancePacketError("maintenance-v0 target drift")
    if baseline_review.get("verdict") != "RECOVERY_CONTROL_PLANE_COMPLETE_ACCEPTED":
        raise MaintenancePacketError("restructured baseline acceptance drift")

    return {
        "schema_id": (
            "toe.maintenance.july_16_19_repository_integration_and_"
            "live_authority_repair.packet.v0"
        ),
        "packet_id": (
            "JULY_16_19_REPOSITORY_INTEGRATION_AND_LIVE_AUTHORITY_"
            "REPAIR_MAINTENANCE_PACKET_20260727_v0"
        ),
        "captured_at_utc": "2026-07-27T00:00:00Z",
        "target": PACKET_TARGET,
        "status": "PREPARED_PENDING_INDEPENDENT_MAINTENANCE_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "independent_maintenance_packet_result_review",
        "authority_basis": {
            "operator_direction": (
                "EXPLICIT_USER_DIRECTED_SEMANTIC_RECONCILIATION_ONTO_"
                "THE_ACCEPTED_RESTRUCTURED_BASELINE_WITH_SCIENTIFIC_"
                "AUTHORITY_FROZEN"
            ),
            "consumed_maintenance_target": CONSUMED_MAINTENANCE_TARGET,
            "maintenance_v0_path": MAINTENANCE_V0_PATH.relative_to(
                REPO_ROOT
            ).as_posix(),
            "maintenance_v0_sha256": _sha256(MAINTENANCE_V0_PATH),
            "restructured_baseline_review_path": BASELINE_REVIEW_PATH.relative_to(
                REPO_ROOT
            ).as_posix(),
            "restructured_baseline_review_sha256": _sha256(BASELINE_REVIEW_PATH),
            "restructured_baseline_verdict": baseline_review["verdict"],
            "restructured_baseline_commit": RESTRUCTURED_BASELINE_COMMIT,
            "preserved_source_integration_tip": SOURCE_INTEGRATION_TIP,
            "reconciliation_mode": (
                "CONTROLLED_SEMANTIC_REPLAY_NOT_BLIND_MERGE"
            ),
            "maintenance_target_rotation_executed": False,
            "independent_review_required_before_execution": True,
        },
        "scientific_authority_freeze": {
            "registry_path": REGISTRY_PATH.relative_to(REPO_ROOT).as_posix(),
            "registry_sha256": _sha256(REGISTRY_PATH),
            "current_target": registry_target,
            "target_rotated": False,
            "scientific_packet_chain_adopted": False,
            "new_physics_authorized": False,
            "yukawa_rerun_authorized": False,
            "sandbox_pipe_repair_and_rerun_authorized": False,
            "preserved_observations_are_validation_evidence": False,
        },
        "external_custody_attestation": {
            "classification": "SAFETY_CUSTODY_ONLY_NOT_SCIENTIFIC_ADOPTION",
            "base_commit": CUSTODY_BASE_COMMIT,
            "manifest_filename": "custody_manifest.json",
            "manifest_sha256": CUSTODY_MANIFEST_SHA256,
            "dirty_extant_archive_filename": (
                "toe_dirty_checkout_extant_files.zip"
            ),
            "dirty_extant_archive_sha256": CUSTODY_ARCHIVE_SHA256,
            "modified_tracked_count": 4,
            "deleted_tracked_count": 3,
            "untracked_file_count": 622,
            "archived_extant_file_count": 626,
            "manifest_row_count": 629,
            "external_location_not_required_for_clean_checkout_validation": True,
        },
        "observed_integration_discrepancy": {
            "registry_scientific_target": registry_target,
            "lean_current_target_observed_before_repair": OBSERVED_LEAN_TARGET,
            "lean_current_authority_observed_before_repair": OBSERVED_LEAN_TARGET,
            "restructured_maintenance_embedded_scientific_target": maintenance[
                "scientific_authority"
            ]["current_target"],
            "source_lineage_scientific_mirror_mismatch_present": True,
            "restructured_baseline_scientific_mirror_mismatch_present": False,
            "restructured_maintenance_embedded_scientific_reference_stale": False,
            "new_python_tranche_validation": {
                "passed": 1362,
                "failed": 45,
                "errors": 4,
            },
            "exhaustive_lean_aggregate_passed": True,
        },
        "authorized_scope": [
            "CLASSIFY_AND_PRESERVE_JULY_16_19_BYTES_WITHOUT_SCIENTIFIC_ADOPTION",
            "SEMANTICALLY_REPLAY_PORTABLE_SOURCE_COMMITS_ONTO_RESTRUCTURED_BASELINE",
            "PRESERVE_RESTRUCTURED_CONTROL_PLANE_AND_CURRENT_HISTORICAL_SEPARATION",
            "RECORD_SOURCE_COMMIT_DISPOSITIONS_AND_TRANSPLANT_RELATIONSHIPS",
            "RECONCILE_SCIENTIFIC_MIRRORS_TO_THE_CANONICAL_REGISTRY_TARGET",
            "CREATE_A_VERSIONED_MAINTENANCE_AUTHORITY_SUCCESSOR",
            "REPAIR_CUMULATIVE_CHECKOUT_TEST_ISOLATION_WITHOUT_WEAKENING_HISTORY",
            "REPAIR_EXPLICIT_AUTHORITY_VALUE_EXTRACTION_AND_COMPARISON",
            "REPAIR_GRAVITATIONAL_CUSTODY_TARGET_DISCOVERY_FAIL_CLOSED",
            "REPAIR_ROOT_README_AND_PUBLIC_ENTRY_DOCUMENT_DISPOSITIONS",
            "RUN_CUMULATIVE_AND_CLEAN_CHECKOUT_VALIDATION",
            "PREPARE_AN_INTEGRATION_RESULT_REVIEW",
            "PREPARE_A_POST_MAINTENANCE_SCIENTIFIC_ADOPTION_OR_REPLAY_DECISION",
        ],
        "prohibited_scope": [
            "ROTATE_SCIENTIFIC_AUTHORITY",
            "ADOPT_JULY_16_19_SCIENTIFIC_PACKET_CHAIN",
            "CREATE_NEW_PHYSICAL_DERIVATION",
            "EXECUTE_OR_RERUN_YUKAWA_SANDBOX",
            "REPAIR_PIPE_AND_RERUN_CONSUMED_SANDBOX",
            "PROMOTE_PRESERVED_OBSERVATIONS_TO_VALIDATION_EVIDENCE",
            "SELECT_TERMINAL_YUKAWA_RESPONSE_DURING_MAINTENANCE",
            "MODIFY_PRODUCTION_KERNEL",
            "CLAIM_PILLAR_OR_SEAM_CLOSURE",
            "PROMOTE_MASTER_ACTION",
            "BLIND_MERGE_DIVERGENT_LINEAGE_TIPS",
            "RESTORE_OBSOLETE_CONTROL_PLANE_OR_LAYOUT",
        ],
        "integration_status_axes": {
            "custody_status": "EXTERNAL_BYTES_AND_MANIFEST_PRESERVED",
            "stage_record_status": "MIXED_REQUIRES_PACKET_LEVEL_CLASSIFICATION",
            "integration_status": "PENDING_INDEPENDENT_MAINTENANCE_REVIEW",
            "scientific_adoption_status": "NOT_ADOPTED",
        },
        "successor_boundary": {
            "independent_review_may_authorize_integration_execution": True,
            "maintenance_completion_may_rotate_scientific_authority": False,
            "post_maintenance_scientific_reconciliation_required": True,
            "terminal_yukawa_selector_is_conditional_not_precommitted": True,
        },
        "claim_ceiling": (
            "This packet prepares repository integration and live-authority repair "
            "as operational maintenance only. It preserves the exact July 12 "
            "scientific target, records external custody of the dirty checkout, and "
            "authorizes no scientific adoption, new derivation, Yukawa rerun, "
            "sandbox repair-and-rerun, production change, validation inference, "
            "pillar or seam closure, or master-action promotion."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_packet(), indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the July 16-19 repository-integration maintenance packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()

    expected = artifact_bytes()
    current = REPORT_PATH.read_bytes() if REPORT_PATH.exists() else None
    if args.write:
        if current != expected:
            REPORT_PATH.write_bytes(expected)
            print(f"wrote {REPORT_PATH.relative_to(REPO_ROOT).as_posix()}")
        else:
            print("repository-integration maintenance packet already current")
        return 0
    if current != expected:
        print("repository-integration maintenance packet drift")
        return 1
    packet = build_packet()
    print(
        "repository-integration maintenance packet OK "
        f"scientific_target={packet['scientific_authority_freeze']['current_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
