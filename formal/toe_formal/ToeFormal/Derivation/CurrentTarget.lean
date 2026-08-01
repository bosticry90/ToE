import ToeFormal.Derivation.ToePostCCFTCoreRecoveryDevelopmentRouteSelectionAuthority

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToePostCCFTCoreRecoveryDevelopmentRouteSelectionAuthority

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := "NONE"
def currentBoundedProgramState : String := "NOT_APPLICABLE"
def currentTargetPhase : String :=
  "POST_CCFT_CORE_RECOVERY_ROUTE_SELECTION_AUTHORIZED_NOT_EXECUTED"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "MINIMAL_CLOSED_CCFT_CORE_DECISION"
def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_records_post_ccft_recovery_route_selection_authority :
    currentLiveTarget = "select_post_ccft_core_recovery_development_route_v0" := by
  rfl

theorem route_selection_authority_is_nonexecuting :
    currentBoundedProgramState = "NOT_APPLICABLE" ∧
    currentTargetPhase =
      "POST_CCFT_CORE_RECOVERY_ROUTE_SELECTION_AUTHORIZED_NOT_EXECUTED" ∧
    currentBoundedAttemptNumber = 0 ∧ candidateRouteCount = 3 ∧
    targetedRecoveryPassLimit = 1 ∧ archiveTraversalAuthorized = false ∧
    ccftV0ProgramPreparationAuthorized = false ∧ programInstalled = false ∧
    programOpened = false ∧ newCCFTPostulateAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
