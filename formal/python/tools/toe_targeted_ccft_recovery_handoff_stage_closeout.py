from __future__ import annotations

"""Review and atomically close targeted CCFT recovery handoff Stage 4."""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    raise SystemExit("Run this tool as a module with .\\py.ps1 -m")

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any

from formal.python.tools.bounded_program_governance import (
    REGISTRY_PATH,
    _registry_json_bytes,
    close_attempt,
    strict_json_loads,
    validate_registry_extension,
    write_event,
)
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry, repair_registry
from formal.python.tools.toe_targeted_ccft_recovery_handoff_stage_execution import (
    CONSTRUCTION_PREPARATION_TARGET,
    MANDATORY_EXIT_TARGET,
    MANIFEST,
    OPEN_EVENT,
    OUTCOME,
    PROGRAM_ID,
    RELEASE_ROOT,
    REPO_ROOT,
    RESULT_PATH,
    STAGE3_RESULT,
    STAGE_ID,
    TARGET,
)


REVIEW_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_REVIEW_v0.json"
)
VALIDATION_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_VALIDATION_v0.json"
)
RESULT_RELATIVE = RESULT_PATH.relative_to(REPO_ROOT).as_posix()
REVIEW_RELATIVE = REVIEW_PATH.relative_to(REPO_ROOT).as_posix()
RESULT_MODULE_PATH = REPO_ROOT / (
    "formal/toe_formal/ToeFormal/Derivation/ToeTargetedCCFTRecoveryHandoffResult.lean"
)
CURRENT_TARGET_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
RESULT_MODULE = "ToeFormal.Derivation.ToeTargetedCCFTRecoveryHandoffResult"
RESULT_KIND = "toe_targeted_ccft_closure_evidence_recovery_mandatory_exit_selected_v0"
STRICT_OUTCOME = (
    "STAGE_4_CLOSED_PASSED_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERED_4_EXACT_CONTRACTS_"
    "HISTORICAL_RECOVERY_COMPLETE_MANDATORY_EXIT_SELECTED_NO_BRANCH_MODEL_CONSTRUCTION_"
    "THEOREM_POSTULATE_PROMOTION_OR_SUCCESSOR_AUTHORITY"
)


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"immutable closeout artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def _result_sha(result: dict[str, Any]) -> str:
    if RESULT_PATH.exists():
        return _sha(RESULT_PATH)
    rendered = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    return hashlib.sha256(rendered.encode("ascii")).hexdigest()


def _head() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _stage() -> dict[str, Any]:
    return _load(MANIFEST)["stages"][3]


def review_result(result: dict[str, Any], captured_at_utc: str) -> dict[str, Any]:
    stage3 = _load(STAGE3_RESULT)
    summary = result["recovered_partial_conflicting_and_absent_contract_summary"]
    boundary = result["nonclaim_boundary"]
    handoff = result["required_nonautomatic_construction_preparation_handoff"]
    checks = {
        "program_stage_target_and_scope_match_manifest": (
            result["program_id"] == PROGRAM_ID
            and result["semantic_stage_id"] == STAGE_ID
            and result["scientific_target"] == TARGET
            and result["scope_hash"] == _stage()["canonical_scope_hash"]
        ),
        "attempt_four_open_event_is_bound": (
            result["attempt_sequence_number"] == 4
            and result["open_event_binding"]["sha256"] == _sha(OPEN_EVENT)
        ),
        "immutable_stage_three_result_is_bound": (
            result["stage_3_input_binding"]["sha256"] == _sha(STAGE3_RESULT)
        ),
        "exactly_one_positive_program_outcome_is_selected": (
            result["exactly_one_program_scientific_outcome"] == OUTCOME
            and result["program_scientific_outcome"] == OUTCOME
            and result["program_outcome_selection_basis"]["alternative_outcome_selected"] is False
        ),
        "four_exact_contracts_materially_exceed_threshold": (
            result["program_outcome_selection_basis"]["exact_contracts_recovered"] == 4
            and result["program_outcome_selection_basis"]["positive_threshold"] == 1
            and result["program_outcome_selection_basis"]["threshold_satisfied"] is True
        ),
        "contract_summary_closes_all_18_checklist_items": (
            summary["checklist_total"] == 18
            and sum(summary[key] for key in (
                "recovered_exact", "conflict_preserved",
                "exact_application_blocked_by_conflict", "exact_configuration_bound",
                "exact_incomplete_parameter_range", "only_nonexact_evidence",
                "no_relevant_evidence",
            )) == 18
        ),
        "postulate_reduction_matches_the_four_stage_three_contracts": (
            result["new_postulate_reduction_summary"]["contract_count"] == 4
            and result["new_postulate_reduction_summary"]["contracts"]
            == stage3["future_new_postulate_reduction_ledger"]
        ),
        "historical_recovery_is_complete_without_exhaustion_claim": (
            result["historical_recovery_boundary"]["ccft_v0_historical_recovery_complete"] is True
            and result["historical_recovery_boundary"]["additional_archive_or_overflow_search_authorized"] is False
            and result["historical_recovery_boundary"]["repository_claim_exhaustion_established"] is False
        ),
        "no_branch_or_combined_model_is_selected": (
            result["branch_readiness_snapshot"]["branch_selected"] == "NONE"
            and result["branch_readiness_snapshot"]["combined_model_authorized"] is False
        ),
        "construction_handoff_is_named_but_not_authorized": (
            handoff["target"] == CONSTRUCTION_PREPARATION_TARGET
            and handoff["preparation_authorized"] is False
            and handoff["installation_authorized"] is False
            and handoff["scientific_stage_authorized"] is False
            and handoff["mandatory_exit_must_complete_first"] is True
        ),
        "mandatory_exit_is_the_only_immediate_successor": (
            result["immediate_successor"]["target"] == MANDATORY_EXIT_TARGET
            and result["immediate_successor"]["selected"] is True
            and result["immediate_successor"]["completed"] is False
        ),
        "no_model_theorem_postulate_promotion_or_physical_claim_occurred": all(
            value is False for value in boundary.values()
        ),
        "terminal_lifecycle_result_passes": result["lifecycle_result"] == "PASSED",
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise ValueError(f"independent Stage 4 review failed: {failed}")
    return {
        "artifact_id": "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_REVIEW_v0",
        "schema_id": "toe.targeted_ccft.recovery_handoff.result_review.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "semantic_stage_id": STAGE_ID,
        "reviewed_result": {"path": RESULT_RELATIVE, "sha256": _result_sha(result)},
        "checks": checks,
        "failed_checks": [],
        "accepted": True,
        "decision": "ACCEPT_POSITIVE_TARGETED_RECOVERY_END_HISTORICAL_RECOVERY_SELECT_MANDATORY_EXIT",
        "scientific_interpretation": {
            "exact_contracts_recovered": 4,
            "historical_recovery_complete": True,
            "cp_nlse_or_lcrd_v3_selected": False,
            "ccft_v0_model_established": False,
            "construction_preparation_authorized": False,
            "theorem_discovery_authorized": False,
            "repository_claim_exhaustion_established": False,
        },
        "status": "PASS",
    }


def _project(registry: dict[str, Any], result_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("open Stage 4 target is not current")
    evidence = "formal/toe_formal/ToeFormal/Derivation/ToeTargetedCCFTRecoveryHandoffResult.lean"
    report = RESULT_RELATIVE
    projection.update({
        "active_lane": MANDATORY_EXIT_TARGET,
        "current_target": MANDATORY_EXIT_TARGET,
        "current_target_kind": RESULT_KIND,
        "current_target_evidence": evidence,
        "current_target_report": report,
        "current_target_outcome": OUTCOME,
        "current_target_strict_outcome": STRICT_OUTCOME,
        "previous_target": TARGET,
        "workstream_id": MANDATORY_EXIT_TARGET,
    })
    registry.update({
        "active_lane": MANDATORY_EXIT_TARGET,
        "ACTIVE_LANE_v0": MANDATORY_EXIT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0": MANDATORY_EXIT_TARGET,
        "PREVIOUS_LIVE_NEXT_TARGET_v0": TARGET,
        "CURRENT_LIVE_TARGET_EVIDENCE_v0": evidence,
        "CURRENT_LIVE_TARGET_REPORT_v0": report,
        "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
        "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT_OUTCOME,
        "CURRENT_LIVE_TARGET_KIND_v0": RESULT_KIND,
        "current_live_next_target": MANDATORY_EXIT_TARGET,
        "current_live_target": MANDATORY_EXIT_TARGET,
        "current_live_target_evidence": evidence,
        "current_live_target_kind": RESULT_KIND,
        "current_live_target_outcome": OUTCOME,
        "current_live_target_report": report,
        "current_live_target_strict_outcome": STRICT_OUTCOME,
        "current_target": MANDATORY_EXIT_TARGET,
        "current_target_evidence": evidence,
        "current_target_kind": RESULT_KIND,
        "current_target_outcome": OUTCOME,
        "current_target_report": report,
        "current_target_strict_outcome": STRICT_OUTCOME,
        "live_next_target": MANDATORY_EXIT_TARGET,
        "live_next_target_evidence": evidence,
        "live_next_target_kind": RESULT_KIND,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_report": report,
        "live_next_target_strict_outcome": STRICT_OUTCOME,
    })
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != TARGET:
        raise ValueError("active workstream is not open Stage 4")
    workstream = active[0]
    workstream.update({
        "workstream_id": MANDATORY_EXIT_TARGET,
        "active_lane": MANDATORY_EXIT_TARGET,
        "authorized_target": MANDATORY_EXIT_TARGET,
        "authorized_next_strict_target": MANDATORY_EXIT_TARGET,
        "selected_next_target": MANDATORY_EXIT_TARGET,
        "selected_next_target_kind": RESULT_KIND,
        "authorization_evidence": evidence,
        "report": report,
        "report_path": report,
        "report_sha256": result_sha256,
        "packet_result": OUTCOME,
        "strict_packet_result": STRICT_OUTCOME,
        "consumed_target": TARGET,
        "consumed_target_kind": "completed_bounded_scientific_stage",
        "queue_scope": "Stage 4 selected positive targeted recovery and the mandatory exit; construction preparation remains separately unauthorized",
        "claim_status": "Historical recovery complete; no branch model equation postulate theorem physical interpretation promotion or successor authority",
    })
    registry["active_lanes"] = [MANDATORY_EXIT_TARGET]
    registry["active_workstream"] = MANDATORY_EXIT_TARGET
    registry["active_workstreams"] = [dict(workstream)]
    if MANDATORY_EXIT_TARGET not in registry["next_strict_target_coverage"]:
        registry["next_strict_target_coverage"].append(MANDATORY_EXIT_TARGET)
        registry["next_strict_target_coverage"].sort()
    registry["current_target_state"].update({
        "active_lane": MANDATORY_EXIT_TARGET,
        "live_next_target": MANDATORY_EXIT_TARGET,
        "previous_live_next_target": TARGET,
        "live_next_target_kind": RESULT_KIND,
        "live_next_target_evidence": evidence,
        "live_next_target_report": report,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_strict_outcome": STRICT_OUTCOME,
    })


def _write_lean() -> None:
    RESULT_MODULE_PATH.write_text(f'''namespace ToeFormal
namespace Derivation
namespace ToeTargetedCCFTRecoveryHandoffResult

def resultId : String := "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_v0"
def reviewId : String := "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_REVIEW_v0"
def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{STAGE_ID}"
def terminalOutcome : String := "{OUTCOME}"
def mandatoryExitTarget : String := "{MANDATORY_EXIT_TARGET}"
def constructionPreparationTarget : String := "{CONSTRUCTION_PREPARATION_TARGET}"

def attemptSequenceNumber : Nat := 4
def exactContractsRecovered : Nat := 4
def cpNlseContractsRecovered : Nat := 1
def lcrdV3ContractsRecovered : Nat := 3
def conflictsPreserved : Nat := 3
def historicalRecoveryComplete : Bool := true
def branchSelected : Bool := false
def ccftV0Constructed : Bool := false
def constructionPreparationAuthorized : Bool := false
def theoremDiscoveryAuthorized : Bool := false
def mandatoryExitSelected : Bool := true
def mandatoryExitCompleted : Bool := false
def repositoryClaimExhaustionEstablished : Bool := false
def reviewAccepted : Bool := true

theorem positive_targeted_recovery_is_selected_and_historical_recovery_ends :
    terminalOutcome = "{OUTCOME}" ∧ attemptSequenceNumber = 4 ∧
    exactContractsRecovered = 4 ∧ cpNlseContractsRecovered = 1 ∧
    lcrdV3ContractsRecovered = 3 ∧ conflictsPreserved = 3 ∧
    historicalRecoveryComplete = true ∧ reviewAccepted = true := by
  decide

theorem mandatory_exit_precedes_nonautomatic_construction_handoff :
    branchSelected = false ∧ ccftV0Constructed = false ∧
    constructionPreparationAuthorized = false ∧ theoremDiscoveryAuthorized = false ∧
    mandatoryExitSelected = true ∧ mandatoryExitCompleted = false ∧
    repositoryClaimExhaustionEstablished = false := by
  decide

end ToeTargetedCCFTRecoveryHandoffResult
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_TARGET_PATH.write_text(f'''import {RESULT_MODULE}

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTRecoveryHandoffResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := mandatoryExitTarget
def currentEvidencePacketId : String := resultId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "CLOSED"
def currentTargetPhase : String := "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_STAGE_4_CLOSED_PASSED"
def currentBoundedAttemptNumber : Nat := attemptSequenceNumber
def lastClosedBoundedSemanticStage : String := semanticStageId
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_is_mandatory_exit_not_construction :
    currentLiveTarget = "{MANDATORY_EXIT_TARGET}" ∧ currentBoundedProgramId = "{PROGRAM_ID}" ∧
    currentBoundedProgramState = "CLOSED" ∧ currentBoundedAttemptNumber = 4 ∧
    exactContractsRecovered = 4 ∧ historicalRecoveryComplete = true ∧
    constructionPreparationAuthorized = false ∧ theoremDiscoveryAuthorized = false ∧
    mandatoryExitSelected = true ∧ mandatoryExitCompleted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_AUTHORITY_PATH.write_text(f'''import ToeFormal.Derivation.CurrentTarget
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

theorem current_authority_tracks_mandatory_exit_without_successor_authority :
    currentTarget = "{MANDATORY_EXIT_TARGET}" ∧ boundedProgramId = "{PROGRAM_ID}" ∧
    boundedProgramState = "CLOSED" ∧ boundedAttemptNumber = 4 ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffResult.historicalRecoveryComplete = true ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffResult.constructionPreparationAuthorized = false ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffResult.theoremDiscoveryAuthorized = false ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffResult.mandatoryExitCompleted = false := by
  native_decide

theorem stage_four_authority_and_review_remain_bound :
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityV0.stageFourOpenAuthorized = true ∧
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityReviewV0.accepted = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''', encoding="utf-8", newline="\n")


def close_stage(*, closed_from_commit: str, captured_at_utc: str) -> str:
    if _head() != closed_from_commit:
        raise ValueError("closed_from_commit must equal current HEAD")
    result = _load(RESULT_PATH)
    review = review_result(result, captured_at_utc)
    _write(REVIEW_PATH, review)
    registry = strict_json_loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    migrated, relative_path, event = close_attempt(
        registry,
        program_id=PROGRAM_ID,
        result_artifact_path=RESULT_RELATIVE,
        review_artifact_path=REVIEW_RELATIVE,
        terminal_result="PASSED",
        closed_from_commit=closed_from_commit,
    )
    event_path = REPO_ROOT / relative_path
    write_event(event_path, event)
    try:
        _project(migrated, _sha(RESULT_PATH))
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        _write_lean()
        validation = {
            "artifact_id": "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_VALIDATION_v0",
            "schema_id": "toe.targeted_ccft.recovery_handoff.validation.v0",
            "captured_at_utc": captured_at_utc,
            "program_id": PROGRAM_ID,
            "semantic_stage_id": STAGE_ID,
            "terminal_outcome": OUTCOME,
            "lifecycle_result": "PASSED",
            "artifact_hashes": {
                "result_sha256": _sha(RESULT_PATH),
                "review_sha256": _sha(REVIEW_PATH),
                "close_event_sha256": _sha(event_path),
                "close_event_hash": event["event_hash"],
            },
            "atomic_close_commit_expected_paths": _stage()["prospective_envelope"]["close_commit_exact_path_set"],
            "scientific_validation": review["checks"],
            "focused_python": {"status": "PENDING_PRECOMMIT"},
            "focused_lean": {"status": "PENDING_PRECOMMIT"},
            "full_lean_aggregate": {"status": "PENDING_PRECOMMIT"},
            "deterministic_generation": {"status": "PENDING_PRECOMMIT"},
            "governance_validation": {
                "event_hash_and_open_close_linkage": "PASS_PRECOMMIT",
                "git_history_chronology": "REQUIRED_POST_COMMIT",
                "precommit_full_history_validator_result": "EXPECTED_SINGLE_FAILURE_CLOSE_ARTIFACT_HAS_ZERO_INTRODUCTION_COMMITS",
            },
            "repository_validation": {
                "exhaustive_python_status": "NOT_CLAIMED_HISTORICAL_DEBT_REMAINS",
                "git_diff_check": "PENDING_PRECOMMIT",
                "reddit_status": "UNTRACKED_AND_UNTOUCHED",
                "tracked_checkout_after_close_commit": "REQUIRED_POST_COMMIT",
            },
            "status": "STAGE_4_ATOMIC_CLOSE_READY_FOR_VALIDATION",
        }
        _write(VALIDATION_PATH, validation)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
    except Exception:
        REVIEW_PATH.unlink(missing_ok=True)
        event_path.unlink(missing_ok=True)
        VALIDATION_PATH.unlink(missing_ok=True)
        RESULT_MODULE_PATH.unlink(missing_ok=True)
        raise
    return relative_path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--closed-from-commit", required=True)
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args(argv)
    print(close_stage(closed_from_commit=args.closed_from_commit, captured_at_utc=args.captured_at_utc))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
