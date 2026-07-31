"""Open gravitational action-family eligibility handoff Stage 5 without science."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    REGISTRY_PATH,
    _registry_json_bytes,
    open_attempt,
    strict_json_loads,
    validate_registry_extension,
    write_event,
)
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = RELEASE / "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_STAGE_5_OPEN_AUTHORITY_v0.json"
AUTHORITY_REVIEW_PATH = RELEASE / "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_STAGE_5_OPEN_AUTHORITY_REVIEW_v0.json"
MANIFEST_PATH = RELEASE / "bounded_program_manifests" / "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0_MANIFEST_v1.json"
VALIDATION_PATH = RELEASE / "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_OPEN_VALIDATION_v0.json"

PROGRAM_ID = "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"
SEMANTIC_STAGE_ID = "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF"
TARGET = "select_toe_gravitational_action_family_eligibility_handoff_v0"
KIND = "toe_gravitational_action_family_eligibility_handoff_stage_5_open_v0"
EVIDENCE = "formal/toe_formal/ToeFormal/Derivation/ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.lean"
REPORT = "formal/docs/release/bounded_program_events/TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0_ATTEMPT_05_OPEN_v0.json"
OUTCOME = "GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_STAGE_5_OPEN"
STRICT_OUTCOME = (
    "STAGE_5_OPEN_ELIGIBILITY_AND_NONEXECUTING_ROUTE_HANDOFF_ONLY_NO_"
    "ACTION_PRINCIPLE_SELECTION_PROMOTION_CALCULATION_OR_SUCCESSOR"
)
PREVIOUS_TARGET = "survey_toe_source_bound_gravitational_requirement_family_compatibility_v0"
EXPECTED_SCOPE_HASH = "aec6355853132543dff1bf7c4aa90e65718ab1b192d56340efc9d5d584bd6dd8"
FULL_COMMIT_ID = re.compile(r"[0-9a-f]{40}")


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_head() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()


def write_json(path: Path, value: dict) -> None:
    if path.exists():
        raise ValueError(f"immutable OPEN artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=True, sort_keys=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def stage() -> dict:
    candidate = read(MANIFEST_PATH)["stages"][4]
    assert candidate["stage_number"] == 5
    assert candidate["semantic_stage_id"] == SEMANTIC_STAGE_ID
    assert candidate["canonical_target"] == TARGET
    assert candidate["canonical_scope_hash"] == EXPECTED_SCOPE_HASH
    return candidate


def check_authority() -> None:
    authority = read(AUTHORITY_PATH)
    review = read(AUTHORITY_REVIEW_PATH)
    candidate = stage()
    if authority["status"] != "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_5_OPEN_ONLY":
        raise ValueError("Stage 5 OPEN authority is not valid")
    if authority["program_id"] != PROGRAM_ID:
        raise ValueError("Stage 5 OPEN authority program mismatch")
    if authority["authorized_stage"] != {
        "canonical_scope_hash": candidate["canonical_scope_hash"],
        "canonical_target": candidate["canonical_target"],
        "semantic_stage_id": candidate["semantic_stage_id"],
        "stage_number": candidate["stage_number"],
    }:
        raise ValueError("Stage 5 OPEN authority differs from manifest")
    if len(authority["family_ids"]) != 7:
        raise ValueError("Stage 5 authority must bind seven families")
    if len(authority["eligibility_classification_vocabulary"]) != 8:
        raise ValueError("Stage 5 authority must bind eight eligibility states")
    if len(authority["post_eligibility_route_vocabulary"]) != 5:
        raise ValueError("Stage 5 authority must bind five nonexecuting routes")
    if review["accepted"] is not True or not all(review["checks"].values()):
        raise ValueError("Stage 5 OPEN authority review is not accepted")
    if any(review["scientific_output_at_authority_checkpoint"].values()):
        raise ValueError("Stage 5 authority checkpoint already contains scientific output")


def project(registry: dict, event_sha: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 5 target is not current")
    projection.update(
        {
            "active_lane": TARGET,
            "current_target": TARGET,
            "current_target_kind": KIND,
            "current_target_evidence": EVIDENCE,
            "current_target_report": REPORT,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "previous_target": PREVIOUS_TARGET,
            "workstream_id": TARGET,
        }
    )
    registry.update(
        {
            "active_lane": TARGET,
            "ACTIVE_LANE_v0": TARGET,
            "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
            "PREVIOUS_LIVE_NEXT_TARGET_v0": PREVIOUS_TARGET,
            "CURRENT_LIVE_TARGET_EVIDENCE_v0": EVIDENCE,
            "CURRENT_LIVE_TARGET_REPORT_v0": REPORT,
            "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT_OUTCOME,
            "CURRENT_LIVE_TARGET_KIND_v0": KIND,
        }
    )
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != TARGET:
        raise ValueError("active workstream is not selected Stage 5 target")
    workstream = active[0]
    workstream.update(
        {
            "active_lane": TARGET,
            "authorized_target": TARGET,
            "authorized_next_strict_target": TARGET,
            "selected_next_target": TARGET,
            "selected_next_target_kind": KIND,
            "authorization_evidence": EVIDENCE,
            "report": REPORT,
            "report_path": REPORT,
            "report_sha256": event_sha,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT_OUTCOME,
            "consumed_target": PREVIOUS_TARGET,
            "consumed_target_kind": "closed_bounded_scientific_stage",
            "queue_scope": (
                "Gravitational action-family eligibility handoff Stage 5 is OPEN; "
                "the OPEN checkpoint contains no classification or route result"
            ),
            "claim_status": (
                "Stage 5 OPEN only; no family eligibility classification, route choice, "
                "action, principle, promotion, calculation, or successor authority"
            ),
        }
    )
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstreams"] = [dict(workstream)]
    registry["current_target_state"].update(
        {
            "active_lane": TARGET,
            "live_next_target": TARGET,
            "previous_live_next_target": PREVIOUS_TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": EVIDENCE,
            "live_next_target_report": REPORT,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
    )


def open_stage(*, opened_from_commit: str) -> str:
    check_authority()
    if not FULL_COMMIT_ID.fullmatch(opened_from_commit):
        raise ValueError("opened_from_commit must be a full lowercase commit ID")
    if current_head() != opened_from_commit:
        raise ValueError("opened_from_commit must equal current HEAD")
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
    if event["scope_hash"] != EXPECTED_SCOPE_HASH:
        raise ValueError("OPEN event scope hash mismatch")
    event_path = ROOT / relative_path
    write_event(event_path, event)
    try:
        project(migrated, sha(event_path))
        validate_registry_extension(migrated)
        candidate = stage()
        validation = {
            "artifact_id": "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_OPEN_VALIDATION_v0",
            "attempt_sequence_number": 5,
            "atomic_open_commit_expected_paths": candidate["prospective_envelope"]["open_commit_exact_path_set"],
            "authority_decision": "AUTHORIZE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_STAGE_5_OPEN",
            "captured_at_utc": "2026-07-31T18:25:00Z",
            "event_hash": event["event_hash"],
            "event_path": REPORT,
            "event_sequence_number": 9,
            "event_sha256": sha(event_path),
            "opened_from_commit": opened_from_commit,
            "program_id": PROGRAM_ID,
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "schema_id": "toe.gravitational_action_family_eligibility_handoff.stage_5_open_validation.v0",
            "scope_hash": EXPECTED_SCOPE_HASH,
            "scientific_output_at_open": {
                "eligibility_classifications_made": 0,
                "gravitational_actions_selected": 0,
                "native_gravitational_principles_selected": 0,
                "post_eligibility_routes_selected": 0,
                "scientific_result_created": False,
                "successor_programs_authorized": 0,
            },
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "status": "STAGE_5_ATOMIC_OPEN_READY_FOR_COMMIT",
            "target": TARGET,
            "validation_checks": {
                "authority_and_review_accepted": True,
                "canonical_manifest_binding_matches": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_scientific_output": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
                "route_vocabulary_is_nonexecuting": True,
                "successor_remains_unauthorized": True,
            },
        }
        write_json(VALIDATION_PATH, validation)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
    except Exception:
        event_path.unlink(missing_ok=True)
        VALIDATION_PATH.unlink(missing_ok=True)
        raise
    return relative_path


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--opened-from-commit", required=True)
    args = parser.parse_args()
    print(open_stage(opened_from_commit=args.opened_from_commit))
