import ToeFormal.Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationBoundedProgramPreparationResultReview

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTNativeMathematicalCoreAndOperationalizationBoundedProgramPreparationResultReview

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := proposedProgramId
def currentBoundedProgramState : String := "PROPOSAL_PREPARED_UNINSTALLED"
def currentTargetPhase : String := "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "NONE"
def lastBoundedTerminalResult : String := "NONE"

theorem current_target_records_prepared_ccft_program_proposal :
    currentLiveTarget = executionTarget := by
  rfl

theorem ccft_program_proposal_is_uninstalled_and_nonexecuting :
    currentBoundedProgramState = "PROPOSAL_PREPARED_UNINSTALLED" ∧
    currentTargetPhase =
      "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY" ∧
    currentBoundedAttemptNumber = 0 ∧
    proposedStageCount = 5 ∧ repairAttemptCount = 0 ∧ programInstalled = false ∧
    scientificStageOpened = false ∧
    ccftMathematicalCoreRecovered = false ∧
    operationalCoherenceDefinitionEstablished = false ∧
    ccftRepresentationFieldOrActionSelected = false ∧
    ccftSeamObservableOrDiscriminatorSelected = false ∧
    evidencePromoted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
