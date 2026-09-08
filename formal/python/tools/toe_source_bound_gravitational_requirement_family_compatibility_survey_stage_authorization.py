"""Open source-bound gravitational compatibility Stage 4 without science."""

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


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = RELEASE_ROOT / (
    "TOE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_"
    "SURVEY_STAGE_4_OPEN_AUTHORITY_v0.json"
)
AUTHORITY_REVIEW_PATH = RELEASE_ROOT / (
    "TOE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_"
    "SURVEY_STAGE_4_OPEN_AUTHORITY_REVIEW_v0.json"
)
MANIFEST_PATH = RELEASE_ROOT / "bounded_program_manifests" / (
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_"
    "SURVEY_V0_MANIFEST_v1.json"
)
VALIDATION_PATH = RELEASE_ROOT / (
    "TOE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_"
    "SURVEY_OPEN_VALIDATION_v0.json"
)
PROGRAM_ID = "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"
SEMANTIC_STAGE_ID = "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY"
TARGET = "survey_toe_source_bound_gravitational_requirement_family_compatibility_v0"
KIND = "toe_source_bound_gravitational_requirement_family_compatibility_survey_stage_4_open_v0"
EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.lean"
)
REPORT = (
    "formal/docs/release/bounded_program_events/"
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_"
    "SURVEY_V0_ATTEMPT_04_OPEN_v0.json"
)
OUTCOME = "SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY_STAGE_4_OPEN"
STRICT_OUTCOME = (
    "STAGE_4_OPEN_ROLE_AWARE_SOURCE_BOUND_COMPATIBILITY_ONLY_NO_ACTION_"
    "INVENTION_SELECTION_PROMOTION_CALCULATION_MASTER_ACTION_OR_STAGE_5"
)
PREVIOUS_STAGE_TARGET = "reconstruct_toe_gravitational_requirement_and_action_family_lineages_v0"
EXPECTED_SCOPE_HASH = "e81613ed69adbe5c5586a2b9fcb22217f721923758f7af0d85a71cce84a51c51"
FULL_COMMIT_ID_PATTERN = re.compile(r"[0-9a-f]{40}")


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _current_head() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _write_json(path: Path, value: dict) -> None:
    if path.exists():
        raise ValueError(f"immutable OPEN artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=True, sort_keys=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def _stage() -> dict:
    manifest = _read(MANIFEST_PATH)
    stage = manifest["stages"][3]
    assert stage["stage_number"] == 4
    assert stage["semantic_stage_id"] == SEMANTIC_STAGE_ID
    assert stage["canonical_target"] == TARGET
    assert stage["canonical_scope_hash"] == EXPECTED_SCOPE_HASH
    return stage


def _check_authority() -> None:
    authority = _read(AUTHORITY_PATH)
    review = _read(AUTHORITY_REVIEW_PATH)
    stage = _stage()
    if authority["status"] != "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_4_OPEN_ONLY":
        raise ValueError("Stage 4 OPEN authority is not valid")
    if authority["program_id"] != PROGRAM_ID:
        raise ValueError("Stage 4 OPEN authority program mismatch")
    if authority["authorized_stage"] != {
        "stage_number": stage["stage_number"],
        "semantic_stage_id": stage["semantic_stage_id"],
        "canonical_target": stage["canonical_target"],
        "canonical_scope_hash": stage["canonical_scope_hash"],
    }:
        raise ValueError("Stage 4 OPEN authority differs from manifest")
    if len(authority["requirement_ids"]) != 10 or len(authority["family_ids"]) != 7:
        raise ValueError("Stage 4 authority must bind ten requirements and seven families")
    if authority["compatibility_cell_count"] != 70:
        raise ValueError("Stage 4 authority must bind seventy cells")
    if len(authority["compatibility_state_vocabulary"]) != 8:
        raise ValueError("Stage 4 authority must bind eight cell states")
    if review["accepted"] is not True or not all(review["checks"].values()):
        raise ValueError("Stage 4 OPEN authority review is not accepted")
    if review["stage_5_authorized"] is not False:
        raise ValueError("Stage 4 authority may not authorize Stage 5")


def _project_current_target(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 4 target is not current")
    projection.update(
        {
            "active_lane": TARGET,
            "current_target": TARGET,
            "current_target_kind": KIND,
            "current_target_evidence": EVIDENCE,
            "current_target_report": REPORT,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "previous_target": PREVIOUS_STAGE_TARGET,
            "workstream_id": TARGET,
        }
    )
    registry.update(
        {
            "active_lane": TARGET,
            "ACTIVE_LANE_v0": TARGET,
            "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
            "PREVIOUS_LIVE_NEXT_TARGET_v0": PREVIOUS_STAGE_TARGET,
            "CURRENT_LIVE_TARGET_EVIDENCE_v0": EVIDENCE,
            "CURRENT_LIVE_TARGET_REPORT_v0": REPORT,
            "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT_OUTCOME,
            "CURRENT_LIVE_TARGET_KIND_v0": KIND,
        }
    )
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != TARGET:
        raise ValueError("active workstream is not selected Stage 4 target")
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
            "report_sha256": report_sha256,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT_OUTCOME,
            "consumed_target": PREVIOUS_STAGE_TARGET,
            "consumed_target_kind": "closed_bounded_scientific_stage",
            "queue_scope": (
                "Source-bound requirement-family compatibility Stage 4 is OPEN; "
                "the OPEN checkpoint contains no populated compatibility cell"
            ),
            "claim_status": (
                "Stage 4 OPEN only; no compatibility result, action invention, "
                "selection, promotion, calculation, master action, or Stage 5"
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
            "previous_live_next_target": PREVIOUS_STAGE_TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": EVIDENCE,
            "live_next_target_report": REPORT,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
    )


def open_stage(*, opened_from_commit: str) -> str:
    _check_authority()
    if not FULL_COMMIT_ID_PATTERN.fullmatch(opened_from_commit):
        raise ValueError("opened_from_commit must be a full lowercase commit ID")
    if _current_head() != opened_from_commit:
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
    event_path = REPO_ROOT / relative_path
    write_event(event_path, event)
    try:
        _project_current_target(migrated, _sha256(event_path))
        validate_registry_extension(migrated)
        stage = _stage()
        validation = {
            "artifact_id": "TOE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY_OPEN_VALIDATION_v0",
            "attempt_sequence_number": 4,
            "atomic_open_commit_expected_paths": stage["prospective_envelope"]["open_commit_exact_path_set"],
            "authority_decision": "AUTHORIZE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY_STAGE_4_OPEN",
            "captured_at_utc": "2026-07-31T16:35:00Z",
            "event_hash": event["event_hash"],
            "event_path": REPORT,
            "event_sha256": _sha256(event_path),
            "event_sequence_number": 7,
            "opened_from_commit": opened_from_commit,
            "program_id": PROGRAM_ID,
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "schema_id": "toe.source_bound_gravitational_requirement_family_compatibility_survey.open_validation.v0",
            "scope_hash": EXPECTED_SCOPE_HASH,
            "scientific_output_at_open": {
                "compatibility_cells_populated": 0,
                "families_eligible_for_native_selection": 0,
                "evidence_promoted": False,
                "gravitational_action_selected": False,
                "gravitational_calculation_started": False,
                "master_action_constructed": False,
                "stage_5_output_created": False,
            },
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "status": "STAGE_4_ATOMIC_OPEN_READY_FOR_COMMIT",
            "target": TARGET,
            "validation_checks": {
                "authority_and_review_accepted": True,
                "canonical_manifest_binding_matches": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_scientific_output": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
                "role_aware_matrix_contract_is_frozen": True,
                "stage_5_remains_unauthorized": True,
            },
        }
        _write_json(VALIDATION_PATH, validation)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
    except Exception:
        event_path.unlink(missing_ok=True)
        VALIDATION_PATH.unlink(missing_ok=True)
        raise
    return relative_path


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--opened-from-commit", required=True)
    arguments = parser.parse_args()
    print(open_stage(opened_from_commit=arguments.opened_from_commit))
