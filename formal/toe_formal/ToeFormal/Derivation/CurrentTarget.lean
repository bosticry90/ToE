import ToeFormal.Derivation.ToeTargetedCCFTRecoveryHandoffResult

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
    currentLiveTarget = "close_toe_targeted_ccft_closure_evidence_recovery_v0_after_bounded_result_v0" ∧ currentBoundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧ currentBoundedAttemptNumber = 4 ∧
    exactContractsRecovered = 4 ∧ historicalRecoveryComplete = true ∧
    constructionPreparationAuthorized = false ∧ theoremDiscoveryAuthorized = false ∧
    mandatoryExitSelected = true ∧ mandatoryExitCompleted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
