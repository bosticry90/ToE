import ToeFormal.Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationBoundedProgramPreparationAuthority

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTNativeMathematicalCoreAndOperationalizationBoundedProgramPreparationAuthority

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := authorizedTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := "NONE"
def currentBoundedProgramState : String := "NOT_APPLICABLE"
def currentTargetPhase : String := "CCFT_PROGRAM_PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "NONE"
def lastBoundedTerminalResult : String := "NONE"

theorem current_target_records_authorized_ccft_program_preparation :
    currentLiveTarget = authorizedTarget := by
  rfl

theorem ccft_program_preparation_authority_is_nonexecuting :
    currentBoundedProgramState = "NOT_APPLICABLE" ∧
    currentTargetPhase = "CCFT_PROGRAM_PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED" ∧
    currentBoundedAttemptNumber = 0 ∧
    proposalPreparationAuthorized = true ∧ programInstalled = false ∧
    scientificStageOpened = false ∧
    ccftMathematicsRecoveredOrAdjudicated = false ∧
    ccftRepresentationOrFieldSelected = false ∧ ccftActionConstructed = false ∧
    ccftSeamOrObservableSelected = false ∧ evidencePromoted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
