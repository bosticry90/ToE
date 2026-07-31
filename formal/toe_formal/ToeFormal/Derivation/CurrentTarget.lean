import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout
import ToeFormal.Derivation.ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationAuthorityV0
import ToeFormal.Derivation.ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationResultReview

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationResultReview

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := scientificTarget
def currentEvidencePacketId : String := resultId
def currentBoundedProgramId : String :=
  "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0"
def currentBoundedProgramState : String := "UNINSTALLED"
def currentTargetPhase : String := "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF"
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_reviewed_positive_principle_program_proposal :
    currentLiveTarget =
      "prepare_toe_positive_native_gravitational_principle_derivation_bounded_program_v0" := by
  rfl

theorem reviewed_positive_principle_program_proposal_is_not_installed_or_opened :
    currentBoundedProgramState = "UNINSTALLED" ∧
    currentTargetPhase =
      "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY" ∧
    currentBoundedAttemptNumber = 0 ∧ proposalPrepared = true ∧
    independentReviewAccepted = true ∧
    programInstalled = false ∧ scientificStageOpened = false ∧
    principleInventoryExecuted = false ∧
    nativeGravitationalPrincipleDerived = false ∧
    gravitationalActionConstructedOrSelected = false ∧
    gravitationalCalculationExecuted = false ∧ evidencePromoted = false ∧
    automaticSuccessorSelected = false ∧
    ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout.mandatoryExitCompleted = true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
