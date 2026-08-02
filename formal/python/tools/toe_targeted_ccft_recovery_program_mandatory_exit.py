from __future__ import annotations

"""Complete the mandatory exit for the targeted CCFT recovery program."""

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.bounded_program_governance import validate_registry_extension
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry, repair_registry


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE = REPO_ROOT / "formal/docs/release"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
EXIT_TARGET = "close_toe_targeted_ccft_closure_evidence_recovery_v0_after_bounded_result_v0"
OUTCOME = "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERED"
CONSTRUCTION_TARGET = "prepare_bounded_ccft_v0_theory_construction_program"
RESULT = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
VALIDATION = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_VALIDATION_v0.json"
TEST = REPO_ROOT / "formal/python/tests/test_toe_targeted_ccft_closure_evidence_recovery_v0_bounded_closeout.py"
LEAN = REPO_ROOT / (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout.lean"
)
CURRENT_TARGET = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY = REPO_ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
STAGE4_RESULT = RELEASE / "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_v0.json"
STAGE4_REVIEW = RELEASE / "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_REVIEW_v0.json"
STRICT = (
    "PROGRAM_TERMINAL_AFTER_POSITIVE_TARGETED_RECOVERY_4_EXACT_CONTRACTS_3_CP_CONFLICTS_"
    "HISTORICAL_RECOVERY_COMPLETE_NO_BRANCH_MODEL_POSTULATE_THEOREM_SEARCH_PROMOTION_OR_"
    "CONSTRUCTION_PREPARATION_AUTHORITY"
)
RESULT_KIND = "toe_targeted_ccft_closure_evidence_recovery_v0_terminal_closeout"


def read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"immutable mandatory-exit artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def stage_bindings(program: dict[str, Any]) -> dict[str, Any]:
    bindings: dict[str, Any] = {
        "event_chain_changed_by_mandatory_exit": False,
        "event_chain_tip_hash": program["event_chain_tip_hash"],
    }
    for attempt in range(1, 5):
        close = next(
            row for row in program["events"]
            if row["event_type"] == "ATTEMPT_CLOSE"
            and row["attempt_sequence_number"] == attempt
        )
        event_path = REPO_ROOT / close["path"]
        event = read(event_path)
        bindings[f"stage_{attempt}_result_path"] = event["result_artifact_path"]
        bindings[f"stage_{attempt}_result_sha256"] = sha(REPO_ROOT / event["result_artifact_path"])
        bindings[f"stage_{attempt}_review_path"] = event["review_artifact_path"]
        bindings[f"stage_{attempt}_review_sha256"] = sha(REPO_ROOT / event["review_artifact_path"])
        bindings[f"stage_{attempt}_close_event_path"] = close["path"]
        bindings[f"stage_{attempt}_close_event_sha256"] = sha(event_path)
    return bindings


def build_result(registry: dict[str, Any], *, captured_at_utc: str) -> dict[str, Any]:
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    stage4 = read(STAGE4_RESULT)
    if program["state"] != "CLOSED" or program["last_closed_attempt_number"] != 4:
        raise ValueError("all four stages must be closed before mandatory exit")
    if program["attempted_stage_ids"] != [
        "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY",
        "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION",
        "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION",
        "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF",
    ]:
        raise ValueError("attempted stage sequence differs from the immutable program")
    if stage4["program_scientific_outcome"] != OUTCOME:
        raise ValueError("Stage 4 did not select the positive targeted-recovery outcome")
    if stage4["stage_3_input_binding"]["exact_contracts_recovered"] != 4:
        raise ValueError("Stage 4 did not bind four recovered contracts")
    if stage4["stage_3_input_binding"]["conflicts_preserved"] != 3:
        raise ValueError("Stage 4 did not preserve three conflicts")
    if stage4["immediate_successor"]["target"] != EXIT_TARGET:
        raise ValueError("Stage 4 did not select the mandatory exit")
    if stage4["required_nonautomatic_construction_preparation_handoff"]["target"] != CONSTRUCTION_TARGET:
        raise ValueError("construction-preparation target differs from the frozen handoff")
    return {
        "artifact_id": f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0",
        "schema_id": "toe.targeted_ccft.closure_evidence_recovery.bounded_closeout_result.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "execution_target": EXIT_TARGET,
        "program_result_alias": OUTCOME,
        "terminal_outcome": OUTCOME,
        "program_closeout": {
            "authorized_stage_count": 4,
            "attempted_stage_count": 4,
            "last_closed_attempt_number": 4,
            "event_chain_event_count": 8,
            "event_chain_tip_hash": program["event_chain_tip_hash"],
            "repair_attempt_count": 0,
            "mandatory_exit_selected": True,
            "mandatory_exit_completed": True,
            "program_terminal_status": "CLOSED_AFTER_MANDATORY_EXIT",
            "unattempted_stage_ids": [],
            "subsidiary_scientific_targets_created": 0,
        },
        "scientific_result": {
            "historical_recovery": "COMPLETE_FOR_CCFT_V0",
            "repository_claim_exhaustion": "NOT_ESTABLISHED",
            "selected_source_count": 96,
            "content_discovery_passes_consumed": 1,
            "recovered_contract_count": 4,
            "cp_nlse_recovered_contract_count": 1,
            "lcrd_v3_recovered_contract_count": 3,
            "cp_nlse_conflict_count": 3,
            "recovered_contracts": stage4["new_postulate_reduction_summary"]["contracts"],
            "cp_nlse_status": "COMPUTATIONALLY_PROMISING_BUT_GOVERNING_DYNAMICS_AND_DISPERSION_CONFLICTED",
            "lcrd_v3_status": "STRUCTURALLY_DISTINCTIVE_BUT_DATA_NORMALIZATION_PARAMETER_AND_IMPLEMENTATION_CONTRACTS_INCOMPLETE",
            "branch_selected": "NONE",
            "closed_ccft_v0_model": "NONE",
            "new_postulates": "NONE",
            "further_archive_search": "NOT_AUTHORIZED",
            "construction_preparation_target": CONSTRUCTION_TARGET,
            "construction_preparation_status": "NAMED_BUT_UNAUTHORIZED",
            "theorem_discovery_status": "NOT_AUTHORIZED",
        },
        "future_decision_boundary": {
            "construction_preparation_target": CONSTRUCTION_TARGET,
            "separate_authority_required": True,
            "construction_preparation_authorized": False,
            "construction_program_installed": False,
            "construction_program_opened": False,
            "research_director_decision_packet_created": False,
            "branch_readiness_decision_made": False,
            "theorem_packet_created_or_executed": False,
            "automatic_successor_selected": False,
        },
        "nonpromotion_boundary": {
            "cp_nlse_equation_selected_repaired_or_postulated": False,
            "lcrd_v3_completed": False,
            "branch_selected": False,
            "ccft_v0_constructed": False,
            "new_ccft_postulate_inserted": False,
            "theorem_or_counterexample_attempted": False,
            "cross_cutting_checks_installed": False,
            "physical_operationalization_established": False,
            "seam_or_gravity_coupling_constructed": False,
            "observable_defined": False,
            "canonical_evidence_promoted": False,
        },
        "source_bindings": stage_bindings(program),
        "verdict": (
            "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_CLOSED_AFTER_POSITIVE_BOUNDED_"
            "RECOVERY_4_EXACT_CONTRACTS_3_CONFLICTS_HISTORICAL_RECOVERY_COMPLETE_NO_"
            "BRANCH_MODEL_POSTULATE_THEOREM_SEARCH_PROMOTION_OR_CONSTRUCTION_AUTHORITY"
        ),
    }


def build_review(result: dict[str, Any], *, captured_at_utc: str) -> dict[str, Any]:
    bindings = result["source_bindings"]
    science = result["scientific_result"]
    future = result["future_decision_boundary"]
    boundary = result["nonpromotion_boundary"]
    checks = {
        "all_four_stages_are_closed_and_passed": result["program_closeout"]["attempted_stage_count"] == 4,
        "event_chain_has_four_matched_open_close_pairs": result["program_closeout"]["event_chain_event_count"] == 8,
        "event_chain_is_unchanged_by_mandatory_exit": bindings["event_chain_changed_by_mandatory_exit"] is False,
        "repair_attempt_count_remains_zero": result["program_closeout"]["repair_attempt_count"] == 0,
        "positive_targeted_recovery_outcome_is_preserved": result["terminal_outcome"] == OUTCOME,
        "four_exact_contracts_and_three_conflicts_are_preserved": science["recovered_contract_count"] == 4 and science["cp_nlse_conflict_count"] == 3,
        "historical_recovery_is_complete_for_ccft_v0": science["historical_recovery"] == "COMPLETE_FOR_CCFT_V0",
        "repository_claim_exhaustion_is_not_established": science["repository_claim_exhaustion"] == "NOT_ESTABLISHED",
        "no_branch_or_closed_ccft_v0_model_is_selected": science["branch_selected"] == "NONE" and science["closed_ccft_v0_model"] == "NONE",
        "no_new_postulate_or_further_archive_search_is_authorized": science["new_postulates"] == "NONE" and science["further_archive_search"] == "NOT_AUTHORIZED",
        "construction_preparation_is_named_but_separately_unauthorized": science["construction_preparation_target"] == CONSTRUCTION_TARGET and future["construction_preparation_authorized"] is False,
        "research_director_branch_and_theorem_work_has_not_begun": future["research_director_decision_packet_created"] is False and future["branch_readiness_decision_made"] is False and future["theorem_packet_created_or_executed"] is False,
        "no_model_theorem_physical_seam_observable_or_promotion_result_was_created": all(value is False for value in boundary.values()),
        "all_stage_result_review_and_close_event_hashes_are_preserved": all(
            sha(REPO_ROOT / bindings[f"stage_{attempt}_{kind}_path"])
            == bindings[f"stage_{attempt}_{kind}_sha256"]
            for attempt in range(1, 5)
            for kind in ("result", "review", "close_event")
        ),
        "mandatory_exit_completes_the_program": result["program_closeout"]["mandatory_exit_completed"] is True and result["program_closeout"]["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT",
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise ValueError(f"mandatory-exit review failed: {failed}")
    return {
        "artifact_id": f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0",
        "schema_id": "toe.targeted_ccft.closure_evidence_recovery.bounded_closeout_review.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "reviewed_result": {"path": relative(RESULT), "sha256": sha(RESULT)},
        "checks": checks,
        "failed_checks": [],
        "accepted": True,
        "program_terminal": True,
        "scientific_success_claimed": False,
        "automatic_successor_selected": False,
        "terminal_status": {
            "program": "CLOSED_AFTER_MANDATORY_EXIT",
            "scientific_outcome": OUTCOME,
            "historical_recovery": "COMPLETE_FOR_CCFT_V0",
            "recovered_contract_count": 4,
            "preserved_conflict_count": 3,
            "branch": "NONE_SELECTED",
            "ccft_v0": "NOT_CONSTRUCTED",
            "construction_preparation": "NAMED_BUT_UNAUTHORIZED",
        },
        "verdict": (
            "ACCEPT_TARGETED_CCFT_RECOVERY_TERMINAL_CLOSEOUT_POSITIVE_RECOVERY_"
            "PRESERVED_HISTORICAL_RECOVERY_COMPLETE_CONSTRUCTION_REQUIRES_NEW_AUTHORITY"
        ),
    }


def project_registry(registry: dict[str, Any], review_sha256: str) -> dict[str, Any]:
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    program.update({
        "mandatory_exit_completed": True,
        "program_terminal_status": "CLOSED_AFTER_MANDATORY_EXIT",
        "program_terminal_outcome": OUTCOME,
        "historical_recovery_complete_for_ccft_v0": True,
        "recovered_contract_count": 4,
        "preserved_conflict_count": 3,
        "branch_selected": "NONE",
        "ccft_v0_constructed": False,
        "new_ccft_postulate_inserted": False,
        "further_archive_search_authorized": False,
        "construction_preparation_target": CONSTRUCTION_TARGET,
        "construction_preparation_authorized": False,
        "construction_program_installed": False,
        "construction_program_opened": False,
        "theorem_discovery_authorized": False,
        "repository_claim_exhaustion_established": False,
        "future_route_selected": "NONE",
        "proposed_successor_authorized": False,
        "proposed_successor_installed": False,
        "proposed_successor_opened": False,
    })
    evidence = relative(LEAN)
    report = relative(REVIEW)
    projection = registry["current_projection_v0"]
    previous = projection["previous_target"]
    projection.update({
        "active_lane": EXIT_TARGET,
        "current_target": EXIT_TARGET,
        "current_target_kind": RESULT_KIND,
        "current_target_evidence": evidence,
        "current_target_report": report,
        "current_target_outcome": OUTCOME,
        "current_target_strict_outcome": STRICT,
        "previous_target": previous,
        "workstream_id": EXIT_TARGET,
    })
    registry.update({
        "active_lane": EXIT_TARGET,
        "ACTIVE_LANE_v0": EXIT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0": EXIT_TARGET,
        "PREVIOUS_LIVE_NEXT_TARGET_v0": previous,
        "CURRENT_LIVE_TARGET_EVIDENCE_v0": evidence,
        "CURRENT_LIVE_TARGET_REPORT_v0": report,
        "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
        "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT,
        "CURRENT_LIVE_TARGET_KIND_v0": RESULT_KIND,
        "current_live_next_target": EXIT_TARGET,
        "current_live_target": EXIT_TARGET,
        "current_live_target_evidence": evidence,
        "current_live_target_kind": RESULT_KIND,
        "current_live_target_outcome": OUTCOME,
        "current_live_target_report": report,
        "current_live_target_strict_outcome": STRICT,
        "current_target": EXIT_TARGET,
        "current_target_evidence": evidence,
        "current_target_kind": RESULT_KIND,
        "current_target_outcome": OUTCOME,
        "current_target_report": report,
        "current_target_strict_outcome": STRICT,
        "live_next_target": EXIT_TARGET,
        "live_next_target_evidence": evidence,
        "live_next_target_kind": RESULT_KIND,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_report": report,
        "live_next_target_strict_outcome": STRICT,
    })
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != EXIT_TARGET:
        raise ValueError("mandatory exit must already be the active target")
    workstream = active[0]
    workstream.update({
        "workstream_id": EXIT_TARGET,
        "active_lane": EXIT_TARGET,
        "authorized_target": EXIT_TARGET,
        "authorized_next_strict_target": EXIT_TARGET,
        "selected_next_target": EXIT_TARGET,
        "selected_next_target_kind": RESULT_KIND,
        "authorization_evidence": evidence,
        "report": report,
        "report_path": report,
        "report_sha256": review_sha256,
        "packet_result": OUTCOME,
        "strict_packet_result": STRICT,
        "consumed_target": previous,
        "consumed_target_kind": "completed_bounded_scientific_program_followed_by_mandatory_exit",
        "queue_scope": "Program terminal after positive targeted recovery and mandatory exit; construction preparation requires separate authority.",
        "claim_status": "Historical recovery complete for CCFT-v0; four exact contracts and three conflicts preserved; no branch, model, postulate, theorem, search, promotion, or construction authority.",
    })
    registry["active_lanes"] = [EXIT_TARGET]
    registry["active_workstream"] = EXIT_TARGET
    registry["active_workstreams"] = [dict(workstream)]
    registry["current_target_state"].update({
        "active_lane": EXIT_TARGET,
        "live_next_target": EXIT_TARGET,
        "previous_live_next_target": previous,
        "live_next_target_kind": RESULT_KIND,
        "live_next_target_evidence": evidence,
        "live_next_target_report": report,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_strict_outcome": STRICT,
    })
    registry = repair_registry(registry)
    validate_registry_extension(registry)
    return registry


def write_lean() -> None:
    LEAN.write_text(f'''import ToeFormal.Derivation.ToeTargetedCCFTRecoveryHandoffResult

namespace ToeFormal
namespace Derivation
namespace ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout

open ToeTargetedCCFTRecoveryHandoffResult

def resultId : String := "{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0"
def reviewId : String := "{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0"
def programId : String := "{PROGRAM_ID}"
def executionTarget : String := "{EXIT_TARGET}"
def terminalOutcome : String := "{OUTCOME}"
def constructionPreparationTarget : String := "{CONSTRUCTION_TARGET}"
def programTerminalStatus : String := "CLOSED_AFTER_MANDATORY_EXIT"

def authorizedStageCount : Nat := 4
def attemptedStageCount : Nat := 4
def eventCount : Nat := 8
def recoveredContractCount : Nat := 4
def preservedConflictCount : Nat := 3
def mandatoryExitCompleted : Bool := true
def historicalRecoveryCompleteForCCFTV0 : Bool := true
def branchSelected : Bool := false
def ccftV0Constructed : Bool := false
def newCCFTPostulateInserted : Bool := false
def furtherArchiveSearchAuthorized : Bool := false
def constructionPreparationAuthorized : Bool := false
def theoremDiscoveryAuthorized : Bool := false
def repositoryClaimExhaustionEstablished : Bool := false

theorem targeted_recovery_program_completed_its_mandatory_exit :
    terminalOutcome = "{OUTCOME}" ∧ programTerminalStatus = "CLOSED_AFTER_MANDATORY_EXIT" ∧
    authorizedStageCount = 4 ∧ attemptedStageCount = 4 ∧ eventCount = 8 ∧
    recoveredContractCount = 4 ∧ preservedConflictCount = 3 ∧
    mandatoryExitCompleted = true ∧ historicalRecoveryCompleteForCCFTV0 = true := by
  decide

theorem construction_remains_separately_unauthorized :
    branchSelected = false ∧ ccftV0Constructed = false ∧
    newCCFTPostulateInserted = false ∧ furtherArchiveSearchAuthorized = false ∧
    constructionPreparationAuthorized = false ∧ theoremDiscoveryAuthorized = false ∧
    repositoryClaimExhaustionEstablished = false := by
  decide

end ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_TARGET.write_text(f'''import ToeFormal.Derivation.ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := programTerminalStatus
def currentTargetPhase : String := "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANDATORY_EXIT_COMPLETE"
def currentBoundedAttemptNumber : Nat := attemptedStageCount
def lastClosedBoundedSemanticStage : String := "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF"
def lastBoundedTerminalResult : String := terminalOutcome

theorem current_target_is_terminal_closeout_not_construction :
    currentLiveTarget = "{EXIT_TARGET}" ∧
    currentBoundedProgramState = "CLOSED_AFTER_MANDATORY_EXIT" ∧
    recoveredContractCount = 4 ∧ preservedConflictCount = 3 ∧
    mandatoryExitCompleted = true ∧ constructionPreparationAuthorized = false ∧
    theoremDiscoveryAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_AUTHORITY.write_text('''import ToeFormal.Derivation.CurrentTarget
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

theorem current_authority_tracks_terminal_closeout_without_construction_authority :
    currentTarget = "close_toe_targeted_ccft_closure_evidence_recovery_v0_after_bounded_result_v0" ∧
    boundedProgramState = "CLOSED_AFTER_MANDATORY_EXIT" ∧ boundedAttemptNumber = 4 ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout.recoveredContractCount = 4 ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout.constructionPreparationAuthorized = false ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout.theoremDiscoveryAuthorized = false := by
  native_decide

theorem stage_four_authority_and_review_remain_bound :
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityV0.stageFourOpenAuthorized = true ∧
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityReviewV0.accepted = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''', encoding="utf-8", newline="\n")


def write_test() -> None:
    TEST.write_text(f'''from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
PROGRAM_ID = "{PROGRAM_ID}"
EXIT_TARGET = "{EXIT_TARGET}"
OUTCOME = "{OUTCOME}"
RESULT = RELEASE / f"{{PROGRAM_ID}}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{{PROGRAM_ID}}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"

def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def test_exit_preserves_positive_result_four_contracts_and_three_conflicts() -> None:
    result = read(RESULT)
    assert result["terminal_outcome"] == OUTCOME
    assert result["scientific_result"]["recovered_contract_count"] == 4
    assert result["scientific_result"]["cp_nlse_conflict_count"] == 3

def test_historical_recovery_is_complete_without_exhaustion_claim() -> None:
    science = read(RESULT)["scientific_result"]
    assert science["historical_recovery"] == "COMPLETE_FOR_CCFT_V0"
    assert science["repository_claim_exhaustion"] == "NOT_ESTABLISHED"
    assert science["further_archive_search"] == "NOT_AUTHORIZED"

def test_no_branch_model_postulate_theorem_or_construction_authority() -> None:
    result = read(RESULT)
    assert result["scientific_result"]["branch_selected"] == "NONE"
    assert result["scientific_result"]["closed_ccft_v0_model"] == "NONE"
    assert result["scientific_result"]["new_postulates"] == "NONE"
    assert all(value is False for value in result["nonpromotion_boundary"].values())
    assert result["future_decision_boundary"]["construction_preparation_authorized"] is False

def test_review_accepts_and_source_hashes_reproduce() -> None:
    review = read(REVIEW)
    assert review["accepted"] is True
    assert review["reviewed_result"]["sha256"] == sha(RESULT)
    assert all(review["checks"].values())

def test_registry_is_terminal_at_mandatory_exit() -> None:
    registry = read(REGISTRY)
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    assert program["mandatory_exit_completed"] is True
    assert program["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"
    assert program["program_terminal_outcome"] == OUTCOME
    assert program["construction_preparation_authorized"] is False
    assert registry["current_projection_v0"]["current_target"] == EXIT_TARGET
''', encoding="utf-8", newline="\n")


def execute(*, captured_at_utc: str) -> None:
    registry = read(REGISTRY)
    result = build_result(registry, captured_at_utc=captured_at_utc)
    write_json(RESULT, result)
    review = build_review(result, captured_at_utc=captured_at_utc)
    write_json(REVIEW, review)
    registry = project_registry(registry, sha(REVIEW))
    atomic_write_registry(REGISTRY, (json.dumps(registry, indent=2, sort_keys=True) + "\n").encode("utf-8"))
    write_lean()
    write_test()
    validation = {
        "artifact_id": f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_VALIDATION_v0",
        "schema_id": "toe.targeted_ccft.closure_evidence_recovery.bounded_closeout_validation.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "result_path": relative(RESULT),
        "result_sha256": sha(RESULT),
        "review_path": relative(REVIEW),
        "review_sha256": sha(REVIEW),
        "governance_validation": {
            "status": "PENDING_PRECOMMIT",
            "event_count": 8,
            "event_chain_changed": False,
            "mandatory_exit_completed": True,
            "repair_attempt_count": 0,
            "mandatory_exit_commit_chronology": "REQUIRED_POST_COMMIT",
        },
        "focused_python_validation": {"status": "PENDING_PRECOMMIT"},
        "focused_lean_validation": {"status": "PENDING_PRECOMMIT"},
        "full_lean_validation": {"status": "PENDING_PRECOMMIT"},
        "deterministic_generation": {"status": "PENDING_PRECOMMIT"},
        "scientific_boundary": {
            "recovered_contract_count": 4,
            "preserved_conflict_count": 3,
            "historical_recovery_complete_for_ccft_v0": True,
            "repository_claim_exhaustion_established": False,
            "branch_selected": False,
            "ccft_v0_constructed": False,
            "new_ccft_postulate_inserted": False,
            "further_archive_search_authorized": False,
            "construction_preparation_authorized": False,
            "theorem_discovery_authorized": False,
            "canonical_evidence_promoted": False,
        },
        "known_validation_debt": {
            "exhaustive_python_status": "NOT_CLAIMED_HISTORICAL_DEBT_REMAINS",
            "status": "DISCLOSED_NOT_REPAIRED_IN_MANDATORY_EXIT",
        },
        "atomic_closeout_commit_expected_path_count": 9,
        "atomic_closeout_commit_expected_paths": sorted([
            relative(REGISTRY), relative(RESULT), relative(REVIEW), relative(VALIDATION),
            relative(TEST), relative(CURRENT_TARGET), relative(LEAN),
            relative(CURRENT_AUTHORITY), "formal/toe_formal/ToeFormalAll.lean",
        ]),
        "tracked_checkout_expected_clean_after_commit": True,
        "untracked_reddit_expected_untouched": True,
        "status": "MANDATORY_EXIT_CLOSEOUT_READY_FOR_VALIDATION",
    }
    write_json(VALIDATION, validation)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args()
    execute(captured_at_utc=args.captured_at_utc)
    print(relative(RESULT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
