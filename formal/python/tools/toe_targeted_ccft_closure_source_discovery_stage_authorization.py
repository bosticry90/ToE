"""Open targeted CCFT closure source-discovery Stage 1 without search output."""

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
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_"
    "STAGE_1_OPEN_AUTHORITY_v0.json"
)
AUTHORITY_REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_"
    "STAGE_1_OPEN_AUTHORITY_REVIEW_v0.json"
)
MANIFEST_PATH = (
    RELEASE_ROOT
    / "bounded_program_manifests"
    / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
)
VALIDATION_PATH = (
    RELEASE_ROOT
    / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_"
    "OPEN_VALIDATION_v0.json"
)
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
SEMANTIC_STAGE_ID = "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY"
TARGET = "discover_toe_targeted_ccft_closure_evidence_sources_v0"
KIND = "toe_targeted_ccft_closure_source_discovery_stage_1_open_v0"
EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeTargetedCCFTClosureSourceDiscoveryAttemptOpen.lean"
)
REPORT = (
    "formal/docs/release/bounded_program_events/"
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_"
    "ATTEMPT_01_OPEN_v0.json"
)
OUTCOME = "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_STAGE_1_OPEN"
STRICT_OUTCOME = (
    "STAGE_1_OPEN_NO_ROOT_TRAVERSAL_CANDIDATE_SELECTION_CONTENT_PASS_CONTRACT_"
    "RECOVERY_EQUATION_REPAIR_POSTULATE_CCFT_V0_CONSTRUCTION_PROMOTION_OR_STAGE_2"
)
EXPECTED_PREVIOUS_TARGET = (
    "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0"
)
EXPECTED_SCOPE_HASH = (
    "d2019a5d75347897cf4648ec88945b2a4cc2209be10ececf6e6c5b7f33d5d6aa"
)
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
    stage = manifest["stages"][0]
    assert stage["stage_number"] == 1
    assert stage["semantic_stage_id"] == SEMANTIC_STAGE_ID
    assert stage["canonical_target"] == TARGET
    assert stage["canonical_scope_hash"] == EXPECTED_SCOPE_HASH
    return stage


def _check_authority() -> None:
    authority = _read(AUTHORITY_PATH)
    review = _read(AUTHORITY_REVIEW_PATH)
    manifest = _read(MANIFEST_PATH)
    stage = _stage()
    if authority["status"] != (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_1_OPEN_ONLY"
    ):
        raise ValueError("Stage 1 OPEN authority is not valid")
    if review["program_id"] != PROGRAM_ID:
        raise ValueError("Stage 1 OPEN authority-review program mismatch")
    if authority["authorized_stage"] != {
        "canonical_scope_hash": stage["canonical_scope_hash"],
        "canonical_target": stage["canonical_target"],
        "semantic_stage_id": stage["semantic_stage_id"],
        "stage_number": stage["stage_number"],
    }:
        raise ValueError("Stage 1 OPEN authority differs from manifest")
    authorized_ids = [item["artifact_id"] for item in authority["authorized_source_set"]]
    if authorized_ids != stage["canonical_scope"]["authorized_inputs"]:
        raise ValueError("Stage 1 authority source set differs from manifest")
    if authority["terminal_outcomes"] != stage["mandatory_terminal_outcomes"]:
        raise ValueError("Stage 1 terminal outcomes differ from manifest")
    if authority["scientific_limits"]["maximum_deep_review_files"] != manifest[
        "workload_caps"
    ]["maximum_deep_review_files"]:
        raise ValueError("Stage 1 file ceiling differs from manifest")
    if authority["scientific_limits"]["targeted_content_search_pass_limit"] != 1:
        raise ValueError("Stage 1 pass limit differs from manifest")
    if authority["selection_contract"]["content_extraction_during_stage_1"]:
        raise ValueError("Stage 1 may not extract contract content")
    for source in authority["evidence_bindings"] + authority["authorized_source_set"]:
        if _sha256(REPO_ROOT / source["path"]) != source["sha256"]:
            raise ValueError(f"Stage 1 authority source hash mismatch: {source['path']}")
    if review["accepted"] is not True or not all(review["checks"].values()):
        raise ValueError("Stage 1 OPEN authority review is not accepted")
    if review["stage_2_authorized"] is not False:
        raise ValueError("Stage 1 authority may not authorize Stage 2")


def _project_current_target(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != EXPECTED_PREVIOUS_TARGET:
        raise ValueError("targeted CCFT preparation target is not current")
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
    if len(active) != 1 or active[0]["workstream_id"] != EXPECTED_PREVIOUS_TARGET:
        raise ValueError("active workstream is not targeted CCFT preparation")
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
            "consumed_target": EXPECTED_PREVIOUS_TARGET,
            "consumed_target_kind": "previous_scientific_authority",
            "queue_scope": (
                "Targeted CCFT source discovery Stage 1 is OPEN; the checkpoint "
                "contains no root traversal candidate selection or scientific result"
            ),
            "claim_status": (
                "Stage 1 OPEN only; no search output content extraction contract "
                "adjudication equation repair postulate CCFT-v0 promotion or Stage 2"
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
    registry["current_target_state"].update(
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
            "artifact_id": (
                "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_"
                "OPEN_VALIDATION_v0"
            ),
            "attempt_sequence_number": 1,
            "atomic_open_commit_expected_paths": stage["prospective_envelope"][
                "open_commit_exact_path_set"
            ],
            "authority_decision": (
                "AUTHORIZE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_"
                "STAGE_1_OPEN"
            ),
            "captured_at_utc": "2026-08-01T04:20:00Z",
            "event_hash": event["event_hash"],
            "event_path": REPORT,
            "event_sha256": _sha256(event_path),
            "event_sequence_number": 1,
            "opened_from_commit": opened_from_commit,
            "program_id": PROGRAM_ID,
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "schema_id": (
                "toe.targeted_ccft_closure_source_discovery_and_custody."
                "stage_1_open_validation.v0"
            ),
            "scope_hash": EXPECTED_SCOPE_HASH,
            "scientific_output_at_open": {
                "archive_or_repository_roots_traversed": 0,
                "candidate_files_discovered": 0,
                "candidate_source_set_created": False,
                "closure_contract_recovered_or_rejected": False,
                "content_passes_consumed": 0,
                "deep_review_files_selected": 0,
                "equation_repaired_or_selected": False,
                "new_ccft_postulate_inserted": False,
                "ccft_v0_constructed": False,
                "evidence_promoted": False,
                "stage_2_output_created": False,
            },
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "status": "STAGE_1_ATOMIC_OPEN_READY_FOR_COMMIT",
            "target": TARGET,
            "validation_checks": {
                "authority_and_review_accepted": True,
                "canonical_manifest_binding_matches": True,
                "event_and_registry_projection_match": True,
                "one_pass_and_zero_repair_controls_match": True,
                "open_checkpoint_contains_no_scientific_output": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID][
                    "state"
                ]
                == "OPEN",
                "stage_2_remains_unauthorized": True,
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
