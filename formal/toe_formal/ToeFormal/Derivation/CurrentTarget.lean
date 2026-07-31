import ToeFormal.Derivation.ToeCCFTPrimaryNativePositiveContentFrontierSelectionAuthority

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTPrimaryNativePositiveContentFrontierSelectionAuthority

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := "NONE"
def currentBoundedProgramState : String := "NOT_APPLICABLE"
def currentTargetPhase : String := "CCFT_FRONTIER_SELECTION_AUTHORIZED_NOT_EXECUTED"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "NONE"
def lastBoundedTerminalResult : String := "NONE"

theorem current_target_records_ccft_frontier_selection_authority :
    currentLiveTarget = "select_ccft_as_primary_native_positive_content_frontier_v0" := by
  rfl

theorem frontier_selection_authority_is_nonexecuting :
    currentBoundedProgramState = "NOT_APPLICABLE" ∧
    currentTargetPhase = "CCFT_FRONTIER_SELECTION_AUTHORIZED_NOT_EXECUTED" ∧
    currentBoundedAttemptNumber = 0 ∧
    ccftProgramPreparationAuthorized = false ∧
    ccftProgramInstalled = false ∧ ccftProgramOpened = false ∧
    scientificCalculationAuthorized = false ∧
    evidencePromotionAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
