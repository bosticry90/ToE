"""Open targeted CCFT closure-contract extraction Stage 2 without extraction output."""

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
    "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_"
    "STAGE_2_OPEN_AUTHORITY_v0.json"
)
AUTHORITY_REVIEW_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_"
    "STAGE_2_OPEN_AUTHORITY_REVIEW_v0.json"
)
MANIFEST_PATH = RELEASE_ROOT / "bounded_program_manifests" / (
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
)
VALIDATION_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_OPEN_VALIDATION_v0.json"
)
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
SEMANTIC_STAGE_ID = "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION"
TARGET = "extract_toe_targeted_ccft_closure_contracts_v0"
KIND = "toe_targeted_ccft_closure_contract_extraction_stage_2_open_v0"
EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeTargetedCCFTClosureContractExtractionAttemptOpen.lean"
)
REPORT = (
    "formal/docs/release/bounded_program_events/"
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_"
    "ATTEMPT_02_OPEN_v0.json"
)
OUTCOME = "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_OPEN"
STRICT_OUTCOME = (
    "STAGE_2_OPEN_96_CAPTURED_SOURCES_ZERO_CONTRACT_RECORDS_NO_SECOND_SEARCH_"
    "OVERFLOW_SUBSTITUTION_ADJUDICATION_EQUATION_REPAIR_INFERENCE_POSTULATE_"
    "CCFT_V0_CONSTRUCTION_PHYSICAL_INTERPRETATION_PROMOTION_OR_STAGE_3"
)
PREVIOUS_STAGE_TARGET = "discover_toe_targeted_ccft_closure_evidence_sources_v0"
EXPECTED_SCOPE_HASH = (
    "bf5a69abf0b8c49b1f5806afa6483a205201103126921af60fef6476348bb0e0"
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
    stage = manifest["stages"][1]
    assert stage["stage_number"] == 2
    assert stage["semantic_stage_id"] == SEMANTIC_STAGE_ID
    assert stage["canonical_target"] == TARGET
    assert stage["canonical_scope_hash"] == EXPECTED_SCOPE_HASH
    return stage


def _check_captured_source_ledger() -> None:
    authority = _read(AUTHORITY_PATH)
    result_path = REPO_ROOT / authority["authorized_input_bindings"][0]["path"]
    result = _read(result_path)
    ledger = result["selected_source_ledger"]
    if len(ledger) != 96:
        raise ValueError("Stage 2 requires exactly 96 selected source captures")
    branch_counts = {"CP_NLSE": 0, "LCRD_V3": 0}
    for record in ledger:
        branch_counts[record["allocation_branch"]] += 1
        capture = record["passive_text_capture"].encode("utf-8")
        if hashlib.sha256(capture).hexdigest() != record["passive_text_capture_sha256"]:
            raise ValueError(f"captured text hash mismatch: {record['record_id']}")
        if record["portable_in_normal_git_history"] is not True:
            raise ValueError(f"selected source is not Git portable: {record['record_id']}")
        if record["scientific_contract_interpretation_performed"] is not False:
            raise ValueError(f"Stage 1 interpreted a contract: {record['record_id']}")
    if branch_counts != {"CP_NLSE": 48, "LCRD_V3": 48}:
        raise ValueError("selected branch allocation differs from 48/48 authority")


def _check_authority() -> None:
    authority = _read(AUTHORITY_PATH)
    review = _read(AUTHORITY_REVIEW_PATH)
    manifest = _read(MANIFEST_PATH)
    stage = _stage()
    if authority["status"] != (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_2_OPEN_ONLY"
    ):
        raise ValueError("Stage 2 OPEN authority is not valid")
    if review["program_id"] != PROGRAM_ID:
        raise ValueError("Stage 2 OPEN authority-review program mismatch")
    if authority["authorized_stage"] != {
        "canonical_scope_hash": stage["canonical_scope_hash"],
        "canonical_target": stage["canonical_target"],
        "semantic_stage_id": stage["semantic_stage_id"],
        "stage_number": stage["stage_number"],
    }:
        raise ValueError("Stage 2 OPEN authority differs from manifest")
    boundary = authority["contract_extraction_boundary"]
    if boundary["selected_source_count"] != 96:
        raise ValueError("Stage 2 authority source count mismatch")
    if boundary["content_search_passes_consumed"] != 1:
        raise ValueError("Stage 2 authority must preserve the consumed pass")
    if boundary["overflow_substitution_authorized"]:
        raise ValueError("Stage 2 may not substitute overflow sources")
    if authority["evidence_strength_vocabulary"] != manifest[
        "evidence_strength_vocabulary"
    ]:
        raise ValueError("Stage 2 evidence vocabulary differs from manifest")
    if authority["frozen_missing_contract_checklists"] != manifest[
        "missing_contract_checklists"
    ]:
        raise ValueError("Stage 2 missing-contract checklists differ from manifest")
    if authority["terminal_outcomes"] != stage["mandatory_terminal_outcomes"]:
        raise ValueError("Stage 2 terminal outcomes differ from manifest")
    for source in authority["evidence_bindings"] + authority["authorized_input_bindings"]:
        if _sha256(REPO_ROOT / source["path"]) != source["sha256"]:
            raise ValueError(f"Stage 2 authority source hash mismatch: {source['path']}")
    _check_captured_source_ledger()
    if review["accepted"] is not True or not all(review["checks"].values()):
        raise ValueError("Stage 2 OPEN authority review is not accepted")
    if review["stage_3_authorized"] is not False:
        raise ValueError("Stage 2 authority may not authorize Stage 3")


def _project_current_target(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 2 target is not current")
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
    if len(active) != 1 or active[0]["workstream_id"] != TARGET:
        raise ValueError("active workstream is not selected Stage 2 target")
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
                "Targeted CCFT closure-contract extraction Stage 2 is OPEN over "
                "the fixed 96 captured sources; the checkpoint contains no extraction result"
            ),
            "claim_status": (
                "Stage 2 OPEN only; zero contract records, no second search, overflow "
                "substitution, adjudication, equation repair, inference, postulate, "
                "CCFT-v0 construction, physical interpretation, promotion, or Stage 3"
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
            "artifact_id": (
                "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_OPEN_VALIDATION_v0"
            ),
            "attempt_sequence_number": 2,
            "atomic_open_commit_expected_paths": stage["prospective_envelope"][
                "open_commit_exact_path_set"
            ],
            "authority_decision": (
                "AUTHORIZE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_OPEN"
            ),
            "captured_at_utc": "2026-08-02T00:10:00Z",
            "event_hash": event["event_hash"],
            "event_path": REPORT,
            "event_sha256": _sha256(event_path),
            "event_sequence_number": 3,
            "opened_from_commit": opened_from_commit,
            "program_id": PROGRAM_ID,
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "schema_id": (
                "toe.targeted_ccft_closure_contract_extraction."
                "stage_2_open_validation.v0"
            ),
            "scope_hash": EXPECTED_SCOPE_HASH,
            "scientific_output_at_open": {
                "captured_selected_sources_bound": 96,
                "closure_contracts_recovered_or_rejected": 0,
                "content_search_passes_consumed": 1,
                "contract_records_extracted": 0,
                "evidence_strength_assignments_created": 0,
                "equation_repaired_or_selected": False,
                "new_archive_or_repository_traversal": False,
                "new_ccft_postulate_inserted": False,
                "ccft_v0_constructed": False,
                "physical_interpretation_established": False,
                "evidence_promoted": False,
                "stage_3_output_created": False,
            },
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "status": "STAGE_2_ATOMIC_OPEN_READY_FOR_COMMIT",
            "target": TARGET,
            "validation_checks": {
                "authority_and_review_accepted": True,
                "canonical_manifest_binding_matches": True,
                "stage_1_result_review_validation_and_close_hashes_match": True,
                "all_96_captured_text_hashes_and_git_portability_bindings_match": True,
                "one_pass_consumed_and_overflow_substitution_prohibited": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_contract_extraction_output": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID][
                    "state"
                ]
                == "OPEN",
                "stage_3_remains_unauthorized": True,
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
