from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    july_16_19_repository_integration_and_live_authority_repair_maintenance_packet_v0
    as packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "JULY_16_19_REPOSITORY_INTEGRATION_AND_LIVE_AUTHORITY_REPAIR_"
    "MAINTENANCE_PACKET_REVIEW_20260727_v0.json"
)
PREPARATION_COMMIT = "fd77dd9259fb3f81fc1fa7b5f7e11fad544ab0d2"
PREPARATION_PARENT = "a099c6867493d48a7aaba2f79bf2e29ecbf2cfd3"
PACKET_SHA256 = "6fb61e29300497346654a22ee24d1b855a9f568b00c3e5cc2f5a895b54f507c7"
GENERATOR_SHA256 = (
    "f5cf2214864ebab19bb181ba3d346082a703a03d5b8e022169765f57d2be152d"
)
SELECTED_NEXT_TARGET = (
    "execute_july_16_19_repository_integration_and_live_authority_repair_v0"
)


class MaintenanceReviewError(RuntimeError):
    pass


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_packet() -> dict[str, Any]:
    expected = packet.artifact_bytes()
    if packet.REPORT_PATH.read_bytes() != expected:
        raise MaintenanceReviewError("maintenance packet artifact drift")
    if _sha256(packet.REPORT_PATH) != PACKET_SHA256:
        raise MaintenanceReviewError("maintenance packet hash drift")
    if _sha256(Path(packet.__file__)) != GENERATOR_SHA256:
        raise MaintenanceReviewError("maintenance packet generator hash drift")
    value = json.loads(expected.decode("utf-8"))
    if not isinstance(value, dict):
        raise MaintenanceReviewError("maintenance packet must be an object")
    return value


def build_review() -> dict[str, Any]:
    reviewed = _load_packet()
    freeze = reviewed["scientific_authority_freeze"]
    custody = reviewed["external_custody_attestation"]
    boundary = reviewed["successor_boundary"]
    prohibited = reviewed["prohibited_scope"]

    gates = {
        "EXACT_PREPARATION_COMMIT_AND_PARENT_RECORDED": True,
        "PACKET_AND_GENERATOR_HASHES_FROZEN": True,
        "EXACT_CANONICAL_SCIENTIFIC_TARGET_PRESERVED": (
            freeze["current_target"] == packet.SCIENTIFIC_TARGET
        ),
        "SCIENTIFIC_TARGET_NOT_ROTATED": freeze["target_rotated"] is False,
        "SCIENTIFIC_CHAIN_NOT_ADOPTED": (
            freeze["scientific_packet_chain_adopted"] is False
        ),
        "NO_NEW_PHYSICS_AUTHORIZED": freeze["new_physics_authorized"] is False,
        "NO_YUKAWA_RERUN_AUTHORIZED": freeze["yukawa_rerun_authorized"] is False,
        "NO_PIPE_REPAIR_AND_RERUN_AUTHORIZED": (
            freeze["sandbox_pipe_repair_and_rerun_authorized"] is False
        ),
        "PRESERVED_OBSERVATIONS_REMAIN_NONVALIDATING": (
            freeze["preserved_observations_are_validation_evidence"] is False
        ),
        "EXTERNAL_CUSTODY_MANIFEST_HASH_BOUND": (
            custody["manifest_sha256"] == packet.CUSTODY_MANIFEST_SHA256
        ),
        "EXTERNAL_CUSTODY_ARCHIVE_HASH_BOUND": (
            custody["dirty_extant_archive_sha256"]
            == packet.CUSTODY_ARCHIVE_SHA256
        ),
        "EXACT_ARCHIVED_EXTANT_COUNT_BOUND": (
            custody["archived_extant_file_count"] == 626
        ),
        "INTEGRATION_EXECUTION_WAS_NOT_SELF_AUTHORIZED": (
            reviewed["authority_basis"]["maintenance_target_rotation_executed"]
            is False
        ),
        "INDEPENDENT_REVIEW_WAS_REQUIRED": (
            reviewed["authority_basis"]["independent_review_required_before_execution"]
            is True
        ),
        "RESTRUCTURED_BASELINE_IS_THE_REPLAY_PARENT": (
            reviewed["authority_basis"]["restructured_baseline_commit"]
            == PREPARATION_PARENT
        ),
        "BLIND_MERGE_IS_PROHIBITED": (
            "BLIND_MERGE_DIVERGENT_LINEAGE_TIPS" in prohibited
        ),
        "MAINTENANCE_CANNOT_ROTATE_SCIENCE": (
            boundary["maintenance_completion_may_rotate_scientific_authority"]
            is False
        ),
        "POST_MAINTENANCE_SCIENTIFIC_RECONCILIATION_REQUIRED": (
            boundary["post_maintenance_scientific_reconciliation_required"]
            is True
        ),
        "TERMINAL_SELECTOR_NOT_PRECOMMITTED": (
            boundary["terminal_yukawa_selector_is_conditional_not_precommitted"]
            is True
        ),
        "PROHIBITED_SCOPE_IS_CLOSED": all(
            item in prohibited
            for item in (
                "ROTATE_SCIENTIFIC_AUTHORITY",
                "ADOPT_JULY_16_19_SCIENTIFIC_PACKET_CHAIN",
                "EXECUTE_OR_RERUN_YUKAWA_SANDBOX",
                "REPAIR_PIPE_AND_RERUN_CONSUMED_SANDBOX",
                "SELECT_TERMINAL_YUKAWA_RESPONSE_DURING_MAINTENANCE",
            )
        ),
    }
    failed = [gate for gate, passed in gates.items() if not passed]
    if failed:
        raise MaintenanceReviewError(f"maintenance review gates failed: {failed}")

    return {
        "schema_id": (
            "toe.maintenance.july_16_19_repository_integration_and_"
            "live_authority_repair.packet.review.v0"
        ),
        "review_id": (
            "JULY_16_19_REPOSITORY_INTEGRATION_AND_LIVE_AUTHORITY_"
            "REPAIR_MAINTENANCE_PACKET_REVIEW_20260727_v0"
        ),
        "captured_at_utc": "2026-07-27T00:00:00Z",
        "target": packet.SELECTED_NEXT_TARGET,
        "verdict": (
            "ACCEPTED_MAINTENANCE_PACKET_AUTHORIZES_BOUNDED_"
            "INTEGRATION_EXECUTION_ONLY"
        ),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "repository_integration_and_live_authority_repair_execution"
        ),
        "preparation_custody": {
            "preparation_commit": PREPARATION_COMMIT,
            "preparation_parent": PREPARATION_PARENT,
            "packet_path": packet.REPORT_PATH.relative_to(REPO_ROOT).as_posix(),
            "packet_sha256": PACKET_SHA256,
            "generator_path": Path(packet.__file__).relative_to(REPO_ROOT).as_posix(),
            "generator_sha256": GENERATOR_SHA256,
        },
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": sum(gates.values()),
            "failure_count": len(failed),
            "rows": [
                {"gate_id": gate, "status": "PASS" if passed else "FAIL"}
                for gate, passed in gates.items()
            ],
        },
        "authorization": {
            "bounded_integration_execution_authorized": True,
            "controlled_semantic_replay_authorized": True,
            "blind_merge_authorized": False,
            "restructured_architecture_must_prevail": True,
            "source_commit_disposition_inventory_required": True,
            "versioned_maintenance_authority_successor_authorized": True,
            "scientific_mirror_repair_authorized": True,
            "packet_level_classification_and_preservation_authorized": True,
            "cumulative_test_isolation_repair_authorized": True,
            "authority_value_comparison_repair_authorized": True,
            "gravitational_custody_gate_repair_authorized": True,
            "readme_front_door_repair_authorized": True,
            "clean_checkout_validation_authorized": True,
            "integration_result_review_required": True,
        },
        "scientific_firewall": {
            "canonical_scientific_target": packet.SCIENTIFIC_TARGET,
            "scientific_target_rotation_authorized": False,
            "scientific_chain_adoption_authorized": False,
            "new_derivation_authorized": False,
            "yukawa_execution_or_rerun_authorized": False,
            "pipe_repair_and_rerun_authorized": False,
            "preserved_observations_validation_use_authorized": False,
            "terminal_yukawa_selection_authorized": False,
            "production_change_authorized": False,
        },
        "result_boundary": {
            "integration_execution_must_preserve_scientific_target": True,
            "integration_result_review_required_before_maintenance_closeout": True,
            "scientific_adoption_or_replay_decision_is_post_maintenance": True,
            "ordered_adoption_is_not_presumed": True,
            "terminal_selector_may_be_unreachable_after_reconciliation": True,
        },
        "claim_ceiling": (
            "This review accepts only the bounded maintenance preparation and "
            "authorizes repository integration execution. It does not rotate "
            "scientific authority, adopt the July 16–19 scientific chain, "
            "authorize a new derivation or Yukawa rerun, permit pipe repair "
            "followed by rerun, validate preserved observations, change "
            "production, select a terminal response, close a pillar or seam, "
            "or promote the master action."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_review(), indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Review the July 16-19 repository-integration maintenance packet."
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
            print("repository-integration maintenance review already current")
        return 0
    if current != expected:
        print("repository-integration maintenance review drift")
        return 1
    review = build_review()
    print(
        "repository-integration maintenance review OK "
        f"gates={review['review_gates']['pass_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
