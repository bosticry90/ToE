import ToeFormal.Derivation.ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout

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
    currentLiveTarget = "close_toe_targeted_ccft_closure_evidence_recovery_v0_after_bounded_result_v0" ∧
    currentBoundedProgramState = "CLOSED_AFTER_MANDATORY_EXIT" ∧
    recoveredContractCount = 4 ∧ preservedConflictCount = 3 ∧
    mandatoryExitCompleted = true ∧ constructionPreparationAuthorized = false ∧
    theoremDiscoveryAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
