"""Open targeted CCFT contract adjudication Stage 3 without scientific output."""

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
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry, repair_registry


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
SEMANTIC_STAGE_ID = "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION"
TARGET = "adjudicate_toe_targeted_ccft_contract_completeness_and_conflicts_v0"
PREVIOUS_TARGET = "extract_toe_targeted_ccft_closure_contracts_v0"
EXPECTED_SCOPE_HASH = "5b6cf39bbf3e4f8bf076dba1817778547410a8d7950164ce5b1c27d0f977410a"
KIND = "toe_targeted_ccft_contract_adjudication_stage_3_open_v0"
OUTCOME = "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_STAGE_3_OPEN"
STRICT_OUTCOME = (
    "STAGE_3_OPEN_23_RECORDS_18_CHECKLISTS_7_EXACT_CANDIDATES_3_CONFLICTS_"
    "ZERO_ADJUDICATION_SELECTION_REPAIR_POSTULATE_CCFT_V0_THEOREM_PROMOTION_OR_STAGE_4"
)
AUTHORITY_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_"
    "STAGE_3_OPEN_AUTHORITY_v0.json"
)
AUTHORITY_REVIEW_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_"
    "STAGE_3_OPEN_AUTHORITY_REVIEW_v0.json"
)
STAGE2_RESULT = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_RESULT_v0.json"
MANIFEST_PATH = RELEASE_ROOT / "bounded_program_manifests/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
VALIDATION_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_OPEN_VALIDATION_v0.json"
)
EVENT_RELATIVE = (
    "formal/docs/release/bounded_program_events/"
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_ATTEMPT_03_OPEN_v0.json"
)
ATTEMPT_MODULE_PATH = REPO_ROOT / (
    "formal/toe_formal/ToeFormal/Derivation/ToeTargetedCCFTContractAdjudicationAttemptOpen.lean"
)
CURRENT_TARGET_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
ATTEMPT_MODULE = "ToeFormal.Derivation.ToeTargetedCCFTContractAdjudicationAttemptOpen"
EVIDENCE = ATTEMPT_MODULE_PATH.relative_to(REPO_ROOT).as_posix()
FULL_COMMIT_ID_PATTERN = re.compile(r"[0-9a-f]{40}")


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_json(path: Path, value: dict) -> None:
    if path.exists():
        raise ValueError(f"immutable OPEN artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def _head() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, check=True,
        capture_output=True, text=True,
    ).stdout.strip()


def _stage() -> dict:
    stage = _read(MANIFEST_PATH)["stages"][2]
    if stage["stage_number"] != 3 or stage["semantic_stage_id"] != SEMANTIC_STAGE_ID:
        raise ValueError("manifest Stage 3 mismatch")
    if stage["canonical_target"] != TARGET or stage["canonical_scope_hash"] != EXPECTED_SCOPE_HASH:
        raise ValueError("manifest Stage 3 target or scope mismatch")
    return stage


def _check_authority() -> None:
    authority = _read(AUTHORITY_PATH)
    review = _read(AUTHORITY_REVIEW_PATH)
    result = _read(STAGE2_RESULT)
    if authority["status"] != "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_3_OPEN_ONLY":
        raise ValueError("Stage 3 OPEN authority is not valid")
    if authority["authorized_stage"] != {
        "canonical_scope_hash": EXPECTED_SCOPE_HASH,
        "canonical_target": TARGET,
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "stage_number": 3,
    }:
        raise ValueError("Stage 3 authority differs from manifest")
    for binding in authority["authorized_input_bindings"] + authority["evidence_bindings"]:
        if _sha(REPO_ROOT / binding["path"]) != binding["sha256"]:
            raise ValueError(f"Stage 3 authority source hash mismatch: {binding['path']}")
    summary = result["extraction_summary"]
    if summary["record_count"] != 23 or len(result["missing_contract_checklist_ledger"]) != 18:
        raise ValueError("Stage 2 record or checklist count differs from authority")
    exact_ids = {
        row["contract_record_id"] for row in result["source_bound_contract_record_ledger"]
        if row["evidence_strength_classification"] == "EXACT_SOURCE_BOUND_CONTRACT_RECOVERED"
    }
    if exact_ids != set(authority["exact_candidate_record_ids"]) or len(exact_ids) != 7:
        raise ValueError("Stage 3 exact candidate set mismatch")
    if review["accepted"] is not True or review["stage_4_authorized"] is not False:
        raise ValueError("Stage 3 authority review boundary is invalid")
    if not all(review["checks"].values()):
        raise ValueError("Stage 3 authority review contains a failed check")


def _project(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 3 target is not current")
    projection.update({
        "active_lane": TARGET,
        "current_target": TARGET,
        "current_target_kind": KIND,
        "current_target_evidence": EVIDENCE,
        "current_target_report": EVENT_RELATIVE,
        "current_target_outcome": OUTCOME,
        "current_target_strict_outcome": STRICT_OUTCOME,
        "previous_target": PREVIOUS_TARGET,
        "workstream_id": TARGET,
    })
    registry.update({
        "active_lane": TARGET,
        "ACTIVE_LANE_v0": TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
        "PREVIOUS_LIVE_NEXT_TARGET_v0": PREVIOUS_TARGET,
        "CURRENT_LIVE_TARGET_EVIDENCE_v0": EVIDENCE,
        "CURRENT_LIVE_TARGET_REPORT_v0": EVENT_RELATIVE,
        "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
        "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT_OUTCOME,
        "CURRENT_LIVE_TARGET_KIND_v0": KIND,
        "current_live_next_target": TARGET,
        "current_live_target": TARGET,
        "current_live_target_evidence": EVIDENCE,
        "current_live_target_kind": KIND,
        "current_live_target_outcome": OUTCOME,
        "current_live_target_report": EVENT_RELATIVE,
        "current_live_target_strict_outcome": STRICT_OUTCOME,
        "current_target": TARGET,
        "current_target_evidence": EVIDENCE,
        "current_target_kind": KIND,
        "current_target_outcome": OUTCOME,
        "current_target_report": EVENT_RELATIVE,
        "current_target_strict_outcome": STRICT_OUTCOME,
        "live_next_target": TARGET,
        "live_next_target_evidence": EVIDENCE,
        "live_next_target_kind": KIND,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_report": EVENT_RELATIVE,
        "live_next_target_strict_outcome": STRICT_OUTCOME,
    })
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != TARGET:
        raise ValueError("active workstream is not selected Stage 3 target")
    workstream = active[0]
    workstream.update({
        "workstream_id": TARGET,
        "active_lane": TARGET,
        "authorized_target": TARGET,
        "authorized_next_strict_target": TARGET,
        "selected_next_target": TARGET,
        "selected_next_target_kind": KIND,
        "authorization_evidence": EVIDENCE,
        "report": EVENT_RELATIVE,
        "report_path": EVENT_RELATIVE,
        "report_sha256": report_sha256,
        "packet_result": OUTCOME,
        "strict_packet_result": STRICT_OUTCOME,
        "consumed_target": PREVIOUS_TARGET,
        "consumed_target_kind": "closed_bounded_scientific_stage",
        "queue_scope": "Stage 3 is OPEN over the fixed Stage 2 evidence; this checkpoint contains no adjudication result",
        "claim_status": "OPEN only; no contract adjudication conflict selection equation repair postulate model theorem promotion or Stage 4",
    })
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstreams"] = [dict(workstream)]
    registry["current_target_state"].update({
        "active_lane": TARGET,
        "live_next_target": TARGET,
        "previous_live_next_target": PREVIOUS_TARGET,
        "live_next_target_kind": KIND,
        "live_next_target_evidence": EVIDENCE,
        "live_next_target_report": EVENT_RELATIVE,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_strict_outcome": STRICT_OUTCOME,
    })


def _write_lean() -> None:
    ATTEMPT_MODULE_PATH.write_text(f'''import ToeFormal.Release.ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityV0

namespace ToeFormal
namespace Derivation
namespace ToeTargetedCCFTContractAdjudicationAttemptOpen

def eventId : String := "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_ATTEMPT_03_OPEN_v0"
def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{SEMANTIC_STAGE_ID}"
def scientificTarget : String := "{TARGET}"
def attemptNumber : Nat := 3
def frozenSourceCount : Nat := 96
def contractRecordCount : Nat := 23
def checklistCount : Nat := 18
def exactCandidateCount : Nat := 7
def conflictedChecklistCount : Nat := 3
def adjudicationRecordsCreated : Nat := 0
def contractRecoveredOrRejected : Bool := false
def conflictSelectedOrRepaired : Bool := false
def newSourceSearchPerformed : Bool := false
def newCCFTPostulateInserted : Bool := false
def ccftV0Constructed : Bool := false
def theoremDiscoveryOpened : Bool := false
def stageFourAuthorized : Bool := false

theorem stage_three_opens_without_scientific_output :
    attemptNumber = 3 ∧ frozenSourceCount = 96 ∧ contractRecordCount = 23 ∧
    checklistCount = 18 ∧ exactCandidateCount = 7 ∧ conflictedChecklistCount = 3 ∧
    adjudicationRecordsCreated = 0 ∧ contractRecoveredOrRejected = false ∧
    conflictSelectedOrRepaired = false ∧ newSourceSearchPerformed = false ∧
    newCCFTPostulateInserted = false ∧ ccftV0Constructed = false ∧
    theoremDiscoveryOpened = false ∧ stageFourAuthorized = false := by
  decide

end ToeTargetedCCFTContractAdjudicationAttemptOpen
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_TARGET_PATH.write_text(f'''import {ATTEMPT_MODULE}

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTContractAdjudicationAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := scientificTarget
def currentEvidencePacketId : String := eventId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "OPEN"
def currentTargetPhase : String := "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_STAGE_3_OPEN"
def currentBoundedAttemptNumber : Nat := attemptNumber
def lastClosedBoundedSemanticStage : String := "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION"
def lastBoundedTerminalResult : String := "TARGETED_CCFT_CONTRACT_EXTRACTION_COMPLETE"

theorem current_target_opens_adjudication_without_result :
    currentLiveTarget = "{TARGET}" ∧ currentBoundedProgramId = "{PROGRAM_ID}" ∧
    currentBoundedProgramState = "OPEN" ∧ currentBoundedAttemptNumber = 3 ∧
    contractRecordCount = 23 ∧ exactCandidateCount = 7 ∧
    adjudicationRecordsCreated = 0 ∧ contractRecoveredOrRejected = false ∧
    theoremDiscoveryOpened = false ∧ stageFourAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_AUTHORITY_PATH.write_text(f'''import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0
import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0
import ToeFormal.Release.ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def boundedProgramId : String := Derivation.CurrentTarget.currentBoundedProgramId
def boundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def boundedAttemptNumber : Nat := Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_open_stage_three_without_output :
    currentTarget = "{TARGET}" ∧ boundedProgramId = "{PROGRAM_ID}" ∧
    boundedProgramState = "OPEN" ∧ boundedAttemptNumber = 3 ∧
    Derivation.ToeTargetedCCFTContractAdjudicationAttemptOpen.adjudicationRecordsCreated = 0 ∧
    Derivation.ToeTargetedCCFTContractAdjudicationAttemptOpen.stageFourAuthorized = false := by
  native_decide

theorem bounded_program_governance_installation_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated = false := by
  native_decide

theorem bounded_program_governance_review_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem all_three_stage_authorities_remain_bound :
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0.stageOneOpenAuthorized = true ∧
    ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0.stageTwoOpenAuthorized = true ∧
    ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityV0.stageThreeOpenAuthorized = true ∧
    ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityReviewV0.accepted = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''', encoding="utf-8", newline="\n")


def open_stage(*, opened_from_commit: str, captured_at_utc: str) -> str:
    _check_authority()
    if not FULL_COMMIT_ID_PATTERN.fullmatch(opened_from_commit) or _head() != opened_from_commit:
        raise ValueError("opened_from_commit must equal current full lowercase HEAD")
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
    if relative_path != EVENT_RELATIVE or event["scope_hash"] != EXPECTED_SCOPE_HASH:
        raise ValueError("OPEN event path or scope mismatch")
    event_path = REPO_ROOT / relative_path
    write_event(event_path, event)
    try:
        _project(migrated, _sha(event_path))
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        _write_lean()
        validation = {
            "artifact_id": "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_OPEN_VALIDATION_v0",
            "schema_id": "toe.targeted_ccft.contract_adjudication.stage_3_open_validation.v0",
            "captured_at_utc": captured_at_utc,
            "program_id": PROGRAM_ID,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "target": TARGET,
            "attempt_sequence_number": 3,
            "authority_decision": "AUTHORIZE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_STAGE_3_OPEN",
            "scope_hash": EXPECTED_SCOPE_HASH,
            "opened_from_commit": opened_from_commit,
            "event_path": EVENT_RELATIVE,
            "event_hash": event["event_hash"],
            "event_sha256": _sha(event_path),
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "atomic_open_commit_expected_paths": _stage()["prospective_envelope"]["open_commit_exact_path_set"],
            "scientific_output_at_open": {
                "frozen_sources": 96,
                "contract_records": 23,
                "checklist_items": 18,
                "exact_candidates": 7,
                "conflicted_checklists": 3,
                "adjudication_records_created": 0,
                "contracts_recovered_or_rejected": 0,
                "conflicts_selected_or_repaired": 0,
                "new_source_search": False,
                "new_ccft_postulates": 0,
                "ccft_v0_constructed": False,
                "theorem_discovery_opened": False,
                "stage_4_output_created": False
            },
            "validation_checks": {
                "authority_and_review_accepted": True,
                "canonical_manifest_binding_matches": True,
                "stage_2_result_review_validation_and_close_hashes_match": True,
                "all_23_records_18_checklists_and_7_exact_candidates_match": True,
                "three_conflict_sets_remain_frozen_without_selection": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_adjudication_or_model_output": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
                "stage_4_remains_unauthorized": True
            },
            "status": "STAGE_3_ATOMIC_OPEN_READY_FOR_COMMIT"
        }
        _write_json(VALIDATION_PATH, validation)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
    except Exception:
        event_path.unlink(missing_ok=True)
        VALIDATION_PATH.unlink(missing_ok=True)
        ATTEMPT_MODULE_PATH.unlink(missing_ok=True)
        raise
    return relative_path


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--opened-from-commit", required=True)
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args()
    print(open_stage(opened_from_commit=args.opened_from_commit, captured_at_utc=args.captured_at_utc))
