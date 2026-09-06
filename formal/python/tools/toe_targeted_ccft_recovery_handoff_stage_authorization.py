"""Open targeted CCFT recovery handoff Stage 4 without selecting a handoff result."""

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
SEMANTIC_STAGE_ID = "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF"
TARGET = "select_toe_post_targeted_ccft_recovery_construction_handoff_v0"
PREVIOUS_TARGET = "adjudicate_toe_targeted_ccft_contract_completeness_and_conflicts_v0"
EXPECTED_SCOPE_HASH = "f6e792eae759877e5e0e6a263834dbdfd96fa8b2a1918a8a038257ab767af254"
KIND = "toe_targeted_ccft_recovery_result_and_construction_handoff_stage_4_open_v0"
OUTCOME = "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_STAGE_4_OPEN"
STRICT_OUTCOME = (
    "STAGE_4_OPEN_4_EXACT_CONTRACTS_3_CONFLICTS_ZERO_HANDOFF_OUTCOME_BRANCH_MODEL_"
    "CONSTRUCTION_THEOREM_SEARCH_POSTULATE_PROMOTION_OR_MANDATORY_EXIT"
)
AUTHORITY_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_"
    "STAGE_4_OPEN_AUTHORITY_v0.json"
)
AUTHORITY_REVIEW_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_"
    "STAGE_4_OPEN_AUTHORITY_REVIEW_v0.json"
)
STAGE3_RESULT = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_RESULT_v0.json"
)
MANIFEST_PATH = RELEASE_ROOT / (
    "bounded_program_manifests/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
)
VALIDATION_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_OPEN_VALIDATION_v0.json"
)
EVENT_RELATIVE = (
    "formal/docs/release/bounded_program_events/"
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_ATTEMPT_04_OPEN_v0.json"
)
ATTEMPT_MODULE_PATH = REPO_ROOT / (
    "formal/toe_formal/ToeFormal/Derivation/ToeTargetedCCFTRecoveryHandoffAttemptOpen.lean"
)
CURRENT_TARGET_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
ATTEMPT_MODULE = "ToeFormal.Derivation.ToeTargetedCCFTRecoveryHandoffAttemptOpen"
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
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _stage() -> dict:
    stage = _read(MANIFEST_PATH)["stages"][3]
    if stage["stage_number"] != 4 or stage["semantic_stage_id"] != SEMANTIC_STAGE_ID:
        raise ValueError("manifest Stage 4 mismatch")
    if stage["canonical_target"] != TARGET or stage["canonical_scope_hash"] != EXPECTED_SCOPE_HASH:
        raise ValueError("manifest Stage 4 target or scope mismatch")
    return stage


def _check_authority() -> None:
    authority = _read(AUTHORITY_PATH)
    review = _read(AUTHORITY_REVIEW_PATH)
    result = _read(STAGE3_RESULT)
    if authority["status"] != "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_4_OPEN_ONLY":
        raise ValueError("Stage 4 OPEN authority is not valid")
    if authority["authorized_stage"] != {
        "canonical_scope_hash": EXPECTED_SCOPE_HASH,
        "canonical_target": TARGET,
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "stage_number": 4,
    }:
        raise ValueError("Stage 4 authority differs from manifest")
    for binding in authority["authorized_input_bindings"] + authority["evidence_bindings"]:
        if _sha(REPO_ROOT / binding["path"]) != binding["sha256"]:
            raise ValueError(f"Stage 4 authority source hash mismatch: {binding['path']}")
    summary = result["adjudication_summary"]
    if summary["exact_contracts_recovered"] != 4 or summary["conflicts_preserved"] != 3:
        raise ValueError("Stage 3 recovery counts differ from authority")
    if len(result["future_new_postulate_reduction_ledger"]) != 4:
        raise ValueError("Stage 3 postulate-reduction ledger differs from authority")
    if result["lifecycle_result"] != "PASSED":
        raise ValueError("Stage 3 did not pass")
    if review["accepted"] is not True or review["scientific_result_created"] is not False:
        raise ValueError("Stage 4 authority review boundary is invalid")
    if not all(review["checks"].values()):
        raise ValueError("Stage 4 authority review contains a failed check")


def _project(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 4 target is not current")
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
        raise ValueError("active workstream is not selected Stage 4 target")
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
        "queue_scope": "Stage 4 is OPEN to select the frozen recovery outcome and nonautomatic handoff; this checkpoint contains no handoff result",
        "claim_status": "OPEN only; no outcome branch model construction theorem search postulate promotion mandatory exit or successor authority",
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
    ATTEMPT_MODULE_PATH.write_text(f'''import ToeFormal.Release.ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityV0

namespace ToeFormal
namespace Derivation
namespace ToeTargetedCCFTRecoveryHandoffAttemptOpen

def eventId : String := "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_ATTEMPT_04_OPEN_v0"
def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{SEMANTIC_STAGE_ID}"
def scientificTarget : String := "{TARGET}"
def attemptNumber : Nat := 4
def exactContractsRecovered : Nat := 4
def conflictsPreserved : Nat := 3
def programOutcomeSelected : Bool := false
def historicalRecoveryClosed : Bool := false
def branchSelected : Bool := false
def ccftV0Constructed : Bool := false
def constructionPreparationAuthorized : Bool := false
def theoremDiscoveryAuthorized : Bool := false
def mandatoryExitExecuted : Bool := false

theorem stage_four_opens_without_handoff_or_construction :
    attemptNumber = 4 ∧ exactContractsRecovered = 4 ∧ conflictsPreserved = 3 ∧
    programOutcomeSelected = false ∧ historicalRecoveryClosed = false ∧
    branchSelected = false ∧ ccftV0Constructed = false ∧
    constructionPreparationAuthorized = false ∧ theoremDiscoveryAuthorized = false ∧
    mandatoryExitExecuted = false := by
  decide

end ToeTargetedCCFTRecoveryHandoffAttemptOpen
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_TARGET_PATH.write_text(f'''import {ATTEMPT_MODULE}

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTRecoveryHandoffAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := scientificTarget
def currentEvidencePacketId : String := eventId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "OPEN"
def currentTargetPhase : String := "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_STAGE_4_OPEN"
def currentBoundedAttemptNumber : Nat := attemptNumber
def lastClosedBoundedSemanticStage : String := "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION"
def lastBoundedTerminalResult : String := "ONE_OR_MORE_EXACT_CCFT_CLOSURE_CONTRACTS_RECOVERED"

theorem current_target_opens_handoff_without_result :
    currentLiveTarget = "{TARGET}" ∧ currentBoundedProgramId = "{PROGRAM_ID}" ∧
    currentBoundedProgramState = "OPEN" ∧ currentBoundedAttemptNumber = 4 ∧
    exactContractsRecovered = 4 ∧ programOutcomeSelected = false ∧
    branchSelected = false ∧ ccftV0Constructed = false ∧
    constructionPreparationAuthorized = false ∧ theoremDiscoveryAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_AUTHORITY_PATH.write_text(f'''import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0
import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0
import ToeFormal.Release.ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityV0
import ToeFormal.Release.ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityV0

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

theorem current_authority_tracks_open_stage_four_without_result :
    currentTarget = "{TARGET}" ∧ boundedProgramId = "{PROGRAM_ID}" ∧
    boundedProgramState = "OPEN" ∧ boundedAttemptNumber = 4 ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffAttemptOpen.programOutcomeSelected = false ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffAttemptOpen.constructionPreparationAuthorized = false ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffAttemptOpen.theoremDiscoveryAuthorized = false := by
  native_decide

theorem all_four_stage_authorities_remain_bound :
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0.stageOneOpenAuthorized = true ∧
    ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0.stageTwoOpenAuthorized = true ∧
    ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityV0.stageThreeOpenAuthorized = true ∧
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityV0.stageFourOpenAuthorized = true ∧
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityReviewV0.accepted = true := by
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
            "artifact_id": "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_OPEN_VALIDATION_v0",
            "schema_id": "toe.targeted_ccft.recovery_handoff.stage_4_open_validation.v0",
            "captured_at_utc": captured_at_utc,
            "program_id": PROGRAM_ID,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "target": TARGET,
            "attempt_sequence_number": 4,
            "authority_decision": "AUTHORIZE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_STAGE_4_OPEN",
            "scope_hash": EXPECTED_SCOPE_HASH,
            "opened_from_commit": opened_from_commit,
            "event_path": EVENT_RELATIVE,
            "event_hash": event["event_hash"],
            "event_sha256": _sha(event_path),
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "atomic_open_commit_expected_paths": _stage()["prospective_envelope"]["open_commit_exact_path_set"],
            "scientific_output_at_open": {
                "exact_contracts_recovered_input": 4,
                "conflicts_preserved_input": 3,
                "program_outcome_selected": False,
                "historical_recovery_closed": False,
                "branch_selected": False,
                "ccft_v0_constructed": False,
                "construction_preparation_authorized": False,
                "theorem_discovery_authorized": False,
                "mandatory_exit_executed": False,
            },
            "validation_checks": {
                "authority_and_review_accepted": True,
                "canonical_manifest_binding_matches": True,
                "stage_3_result_review_validation_and_close_hashes_match": True,
                "four_exact_contracts_and_three_conflicts_match": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_handoff_or_model_output": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
                "mandatory_exit_not_executed": True,
                "construction_and_theorem_discovery_remain_unauthorized": True,
            },
            "status": "STAGE_4_ATOMIC_OPEN_READY_FOR_COMMIT",
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
