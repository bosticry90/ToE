from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    COHERENCE_ONTOLOGY_PROGRAM_ID,
    REGISTRY_PATH,
    _registry_json_bytes,
    open_attempt,
    strict_json_loads,
    validate_registry_extension,
    write_event,
)
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_CONTROLLED_COHERENCE_CLAIM_INVENTORY_STAGE_1_OPEN_AUTHORITY_20260729_v0.json"
)
AUTHORITY_REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_CONTROLLED_COHERENCE_CLAIM_INVENTORY_STAGE_1_OPEN_AUTHORITY_REVIEW_20260729_v0.json"
)
DEPENDENCY_PATH = (
    RELEASE_ROOT
    / "TOE_NATIVE_COHERENCE_STAGE_1_DEPENDENCY_IMPACT_CHECK_20260729_v0.json"
)
PROGRAM_ID = COHERENCE_ONTOLOGY_PROGRAM_ID
SEMANTIC_STAGE_ID = "CONTROLLED_COHERENCE_CLAIM_INVENTORY"
TARGET = "inventory_toe_native_controlled_coherence_claims_v0"
KIND = "toe_native_controlled_coherence_claim_inventory_stage_1_open_v0"
EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeNativeControlledCoherenceClaimInventoryAttemptOpen.lean"
)
REPORT = (
    "formal/docs/release/bounded_program_events/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_ATTEMPT_01_OPEN_v0.json"
)
OUTCOME = "CONTROLLED_COHERENCE_CLAIM_INVENTORY_STAGE_1_OPEN"
STRICT_OUTCOME = (
    "STAGE_1_OPEN_NO_CLAIM_INVENTORY_REPRESENTATION_FIELD_ACTION_SEAM_"
    "PILLAR_OBSERVABLE_OR_EMPIRICAL_CLAIM"
)
EXPECTED_PREVIOUS_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_bounded_program_v0"
)
REPORT_SHA256 = (
    "5f21d6c665d6eb4ec421b2b958a38d815610af99060b87c4361858c92d8e2755"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _check_authority() -> None:
    authority = _read(AUTHORITY_PATH)
    review = _read(AUTHORITY_REVIEW_PATH)
    dependency = _read(DEPENDENCY_PATH)
    if authority["status"] != (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_1_OPEN_ONLY"
    ):
        raise ValueError("Stage 1 OPEN authority is not valid")
    if review["accepted"] is not True or not all(review["checks"].values()):
        raise ValueError("Stage 1 OPEN authority review is not accepted")
    if dependency["stage_1_open_permitted_by_dependency_check"] is not True:
        raise ValueError("Stage 1 dependency-impact check blocks OPEN")


def _project_current_target(registry: dict) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != EXPECTED_PREVIOUS_TARGET:
        raise ValueError("program-preparation target is not current")
    projection.update(
        {
            "active_lane": TARGET,
            "current_target": TARGET,
            "current_target_kind": KIND,
            "current_target_evidence": EVIDENCE,
            "current_target_report": REPORT,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "previous_target": EXPECTED_PREVIOUS_TARGET,
            "workstream_id": TARGET,
        }
    )
    registry.update(
        {
            "active_lane": TARGET,
            "ACTIVE_LANE_v0": TARGET,
            "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
            "PREVIOUS_LIVE_NEXT_TARGET_v0": EXPECTED_PREVIOUS_TARGET,
            "CURRENT_LIVE_TARGET_EVIDENCE_v0": EVIDENCE,
            "CURRENT_LIVE_TARGET_REPORT_v0": REPORT,
            "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT_OUTCOME,
            "CURRENT_LIVE_TARGET_KIND_v0": KIND,
        }
    )
    previous_active = [
        item for item in registry["workstreams"] if item.get("status") == "active"
    ]
    if len(previous_active) != 1:
        raise ValueError("expected exactly one active predecessor workstream")
    workstream = previous_active[0]
    if workstream["workstream_id"] != EXPECTED_PREVIOUS_TARGET:
        raise ValueError("active workstream is not the program-preparation target")
    workstream.update(
        {
            "workstream_id": TARGET,
            "active_lane": TARGET,
            "authorized_target": TARGET,
            "authorized_next_strict_target": TARGET,
            "selected_next_target": TARGET,
            "selected_next_target_kind": KIND,
            "authorization_evidence": EVIDENCE,
            "report": REPORT,
            "report_path": REPORT,
            "report_sha256": REPORT_SHA256,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT_OUTCOME,
            "consumed_target": EXPECTED_PREVIOUS_TARGET,
            "consumed_target_kind": "previous_scientific_authority",
            "queue_scope": (
                "Stage 1 controlled coherence claim inventory is OPEN; "
                "no scientific output exists in the OPEN checkpoint"
            ),
            "claim_status": (
                "Stage 1 OPEN only; no claim inventory, representation, field, "
                "action, seam, pillar, observable, or empirical claim"
            ),
        }
    )
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstreams"] = [dict(workstream)]
    coverage = registry["next_strict_target_coverage"]
    if TARGET not in coverage:
        coverage.append(TARGET)
        coverage.sort()
    state = registry["current_target_state"]
    state.update(
        {
            "active_lane": TARGET,
            "live_next_target": TARGET,
            "previous_live_next_target": EXPECTED_PREVIOUS_TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": EVIDENCE,
            "live_next_target_report": REPORT,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
    )


def open_stage(*, opened_from_commit: str) -> str:
    _check_authority()
    registry_bytes = REGISTRY_PATH.read_bytes()
    registry = strict_json_loads(registry_bytes.decode("utf-8"))
    migrated, relative_path, event = open_attempt(
        registry,
        registry_bytes=registry_bytes,
        program_id=PROGRAM_ID,
        semantic_stage_id=SEMANTIC_STAGE_ID,
        target=TARGET,
        opened_from_commit=opened_from_commit,
    )
    _project_current_target(migrated)
    event_path = REPO_ROOT / relative_path
    write_event(event_path, event)
    try:
        validate_registry_extension(migrated)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
    except Exception:
        event_path.unlink(missing_ok=True)
        raise
    return relative_path


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--opened-from-commit", required=True)
    args = parser.parse_args()
    print(open_stage(opened_from_commit=args.opened_from_commit))
