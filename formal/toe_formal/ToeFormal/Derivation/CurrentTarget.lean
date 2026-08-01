import ToeFormal.Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := proposedProgramId
def currentBoundedProgramState : String := "PROPOSAL_PREPARED_UNINSTALLED"
def currentTargetPhase : String :=
  "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "MINIMAL_CLOSED_CCFT_CORE_DECISION"
def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_records_prepared_targeted_recovery_program_proposal :
    currentLiveTarget =
      "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0" := by
  rfl

theorem prepared_proposal_is_bounded_uninstalled_and_nonexecuting :
    currentBoundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    currentBoundedProgramState = "PROPOSAL_PREPARED_UNINSTALLED" ∧
    currentTargetPhase =
      "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY" ∧
    currentBoundedAttemptNumber = 0 ∧ proposedStageCount = 4 ∧
    searchPassLimit = 1 ∧ repairAttemptCount = 0 ∧ programInstalled = false ∧
    scientificStageOpened = false ∧ archiveSearchExecuted = false ∧
    contractRecovered = false ∧
    ccftEquationRepairedOrSelected = false ∧ newCCFTPostulateInserted = false ∧
    ccftV0Constructed = false ∧ constructionPreparationAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
