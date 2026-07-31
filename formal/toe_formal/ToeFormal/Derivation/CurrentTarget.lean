import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout
import ToeFormal.Derivation.ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationAuthorityV0
import ToeFormal.Derivation.ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationResultReview
import ToeFormal.Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationResultReview

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := scientificTarget
def currentEvidencePacketId : String :=
  "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_PROGRAM_GOVERNANCE_INSTALLATION_v0"
def currentBoundedProgramId : String :=
  "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0"
def currentBoundedProgramState : String := "UNOPENED"
def currentTargetPhase : String :=
  "PROGRAM_INSTALLED_AWAITING_SEPARATE_STAGE_1_AUTHORITY"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF"
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_installed_positive_principle_program :
    currentLiveTarget =
      "prepare_toe_positive_native_gravitational_principle_derivation_bounded_program_v0" := by
  rfl

theorem positive_principle_program_is_installed_but_unopened :
    currentBoundedProgramState = "UNOPENED" ∧
    currentTargetPhase =
      "PROGRAM_INSTALLED_AWAITING_SEPARATE_STAGE_1_AUTHORITY" ∧
    currentBoundedAttemptNumber = 0 ∧ proposalPrepared = true ∧
    independentReviewAccepted = true ∧
    Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0.programInstalled =
      true ∧
    Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0.programOpened =
      false ∧
    scientificStageOpened = false ∧
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
