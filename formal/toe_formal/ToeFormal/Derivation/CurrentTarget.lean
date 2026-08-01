import ToeFormal.Derivation.ToePostCCFTCoreRecoveryDevelopmentRouteSelectionResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToePostCCFTCoreRecoveryDevelopmentRouteSelectionResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := "NONE"
def currentBoundedProgramState : String := "NOT_APPLICABLE"
def currentTargetPhase : String :=
  "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_PROGRAM_PREPARATION_AWAITING_AUTHORITY"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "MINIMAL_CLOSED_CCFT_CORE_DECISION"
def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_is_targeted_recovery_program_preparation :
    currentLiveTarget =
      "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0" := by
  rfl

theorem route_selection_does_not_execute_recovery_or_construction :
    currentBoundedProgramState = "NOT_APPLICABLE" ∧
    currentTargetPhase =
      "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_PROGRAM_PREPARATION_AWAITING_AUTHORITY" ∧
    currentBoundedAttemptNumber = 0 ∧ targetedRecoveryPassLimit = 1 ∧
    targetedRecoveryPreparationAuthorized = false ∧ archiveTraversalStarted = false ∧
    automaticSecondSearchAuthorized = false ∧
    constructionHandoffRequiredAfterEitherOutcome = true ∧
    constructionPreparationAuthorizedNow = false ∧
    closedCCFTModelConstructed = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
