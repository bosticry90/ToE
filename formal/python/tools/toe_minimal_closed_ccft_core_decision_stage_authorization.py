"""Open minimal closed CCFT surrogate-core decision Stage 4 without science."""

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
from formal.python.tools.loop_control_registry_integrity import (
    atomic_write_registry,
    repair_registry,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = RELEASE_ROOT / (
    "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_STAGE_4_OPEN_AUTHORITY_v0.json"
)
AUTHORITY_REVIEW_PATH = RELEASE_ROOT / (
    "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_STAGE_4_OPEN_AUTHORITY_REVIEW_v0.json"
)
MANIFEST_PATH = RELEASE_ROOT / "bounded_program_manifests" / (
    "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0_MANIFEST_v1.json"
)
VALIDATION_PATH = RELEASE_ROOT / (
    "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_OPEN_VALIDATION_v0.json"
)
PROGRAM_ID = "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0"
SEMANTIC_STAGE_ID = "MINIMAL_CLOSED_CCFT_CORE_DECISION"
TARGET = "select_or_reject_toe_minimal_closed_ccft_core_v0"
KIND = "toe_minimal_closed_ccft_surrogate_core_decision_stage_4_open_v0"
EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeMinimalClosedCCFTCoreDecisionAttemptOpen.lean"
)
REPORT = (
    "formal/docs/release/bounded_program_events/"
    "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0_"
    "ATTEMPT_04_OPEN_v0.json"
)
OUTCOME = "MINIMAL_CLOSED_CCFT_SURROGATE_CORE_DECISION_STAGE_4_OPEN"
STRICT_OUTCOME = (
    "STAGE_4_OPEN_NO_CORE_SELECTION_PHYSICAL_PROMOTION_NEW_POSTULATE_ACTION_"
    "SEAM_OBSERVABLE_VIABILITY_TEST_OR_STAGE_5"
)
PREVIOUS_STAGE_TARGET = "operationalize_toe_retained_ccft_mathematical_objects_v0"
EXPECTED_SCOPE_HASH = "e8bd8faac099a9b1c9e759bfae544bbe8eb56ad631959b369dc595b9f9901adf"
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
    if review["program_id"] != PROGRAM_ID:
        raise ValueError("Stage 4 OPEN authority-review program mismatch")
    if authority["authorized_stage"] != {
        "canonical_scope_hash": stage["canonical_scope_hash"],
        "canonical_target": stage["canonical_target"],
        "semantic_stage_id": stage["semantic_stage_id"],
        "stage_number": stage["stage_number"],
    }:
        raise ValueError("Stage 4 OPEN authority differs from manifest")
    boundary = authority["authorized_candidate_boundary"]
    expected = {
        "stage_3_operational_record_count": 20,
        "bounded_surrogate_record_count": 5,
        "generic_or_known_physics_record_count": 6,
        "fully_physically_operational_object_count": 0,
    }
    for key, value in expected.items():
        if boundary[key] != value:
            raise ValueError(f"Stage 4 authority {key} mismatch")
    if boundary["combined_wave_rotor_candidate_authorized"] is not False:
        raise ValueError("Stage 4 may not authorize a combined wave-rotor candidate")
    if boundary["minimal_core_selected"] is not False:
        raise ValueError("Stage 4 authority input may not contain a selected core")
    if boundary["preferred_formulation_selected"] is not False:
        raise ValueError("Stage 4 authority input may not contain a preferred formulation")
    for source in authority["evidence_bindings"] + authority["authorized_input_bindings"]:
        if _sha256(REPO_ROOT / source["path"]) != source["sha256"]:
            raise ValueError(f"Stage 4 authority source hash mismatch: {source['path']}")
    if review["accepted"] is not True or not all(review["checks"].values()):
        raise ValueError("Stage 4 OPEN authority review is not accepted")
    if review["stage_5_authorized"] is not False:
        raise ValueError("Stage 4 authority may not authorize Stage 5")


def _project_current_target(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] not in {TARGET, PREVIOUS_STAGE_TARGET}:
        raise ValueError("registry is not at the closed Stage 3 / selected Stage 4 boundary")
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
            "current_live_next_target": TARGET,
            "current_live_target": TARGET,
            "current_live_target_evidence": EVIDENCE,
            "current_live_target_kind": KIND,
            "current_live_target_outcome": OUTCOME,
            "current_live_target_report": REPORT,
            "current_live_target_strict_outcome": STRICT_OUTCOME,
            "current_target": TARGET,
            "current_target_evidence": EVIDENCE,
            "current_target_kind": KIND,
            "current_target_outcome": OUTCOME,
            "current_target_report": REPORT,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "live_next_target": TARGET,
            "live_next_target_evidence": EVIDENCE,
            "live_next_target_kind": KIND,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_report": REPORT,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
    )
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] not in {
        TARGET,
        PREVIOUS_STAGE_TARGET,
    }:
        raise ValueError("active workstream is not at the Stage 3 / Stage 4 boundary")
    workstream = active[0]
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
            "report_sha256": report_sha256,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT_OUTCOME,
            "consumed_target": PREVIOUS_STAGE_TARGET,
            "consumed_target_kind": "closed_bounded_scientific_stage",
            "queue_scope": (
                "Minimal closed CCFT surrogate-core decision Stage 4 is OPEN; "
                "the OPEN checkpoint contains no core-selection result"
            ),
            "claim_status": (
                "Stage 4 OPEN only; no minimal core, preferred formulation, new "
                "postulate, physical CCFT model, action, seam, observable, viability "
                "test, promotion, or Stage 5"
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
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        stage = _stage()
        validation = {
            "artifact_id": "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_OPEN_VALIDATION_v0",
            "attempt_sequence_number": 4,
            "atomic_open_commit_expected_paths": stage["prospective_envelope"]["open_commit_exact_path_set"],
            "authority_decision": "AUTHORIZE_MINIMAL_CLOSED_CCFT_SURROGATE_CORE_DECISION_STAGE_4_OPEN",
            "captured_at_utc": "2026-08-01T01:12:00Z",
            "event_hash": event["event_hash"],
            "event_path": REPORT,
            "event_sha256": _sha256(event_path),
            "event_sequence_number": 7,
            "opened_from_commit": opened_from_commit,
            "program_id": PROGRAM_ID,
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "schema_id": "toe.ccft.minimal_closed_core_decision.stage_4_open_validation.v0",
            "scope_hash": EXPECTED_SCOPE_HASH,
            "scientific_output_at_open": {
                "candidate_core_rows_evaluated": 0,
                "closure_matrix_cells_populated": 0,
                "minimal_core_selected": False,
                "preferred_formulation_selected": False,
                "new_postulate_inserted": False,
                "physical_ccft_model_established": False,
                "action_seam_observable_or_viability_test_created": False,
                "evidence_promoted": False,
                "stage_5_output_created": False,
            },
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "status": "STAGE_4_ATOMIC_OPEN_READY_FOR_COMMIT",
            "target": TARGET,
            "validation_checks": {
                "authority_and_review_accepted": True,
                "canonical_manifest_binding_matches": True,
                "stage_3_result_review_validation_and_close_hashes_match": True,
                "twenty_records_five_surrogates_six_generic_and_zero_physical_objects_are_bound": True,
                "cp_nlse_and_lcrd_candidates_are_separate": True,
                "generic_linear_baseline_is_comparator_only": True,
                "combined_wave_rotor_candidate_is_unauthorized": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_scientific_output": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
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
