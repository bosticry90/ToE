import ToeFormal.Derivation.ToeCCFTPrimaryNativePositiveContentFrontierSelectionResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTPrimaryNativePositiveContentFrontierSelectionResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := "NONE"
def currentBoundedProgramState : String := "NOT_APPLICABLE"
def currentTargetPhase : String := "CCFT_BOUNDED_PROGRAM_PREPARATION_SELECTED_NOT_EXECUTED"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "NONE"
def lastBoundedTerminalResult : String := "NONE"

theorem current_target_records_selected_ccft_program_preparation :
    currentLiveTarget =
      "prepare_toe_ccft_native_mathematical_core_and_operationalization_bounded_program_v0" := by
  rfl

theorem selected_ccft_preparation_target_is_nonexecuting :
    currentBoundedProgramState = "NOT_APPLICABLE" ∧
    currentTargetPhase = "CCFT_BOUNDED_PROGRAM_PREPARATION_SELECTED_NOT_EXECUTED" ∧
    currentBoundedAttemptNumber = 0 ∧
    programPreparationAuthorized = false ∧ programProposalPrepared = false ∧
    programInstalled = false ∧ programOpened = false ∧
    ccftRepresentationSelected = false ∧ ccftActionConstructed = false ∧
    ccftSeamSelectedOrClosed = false ∧ evidencePromoted = false ∧
    newScientificCalculationExecuted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
