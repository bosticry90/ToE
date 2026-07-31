import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout
import ToeFormal.Derivation.ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationAuthorityV0

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationAuthorityV0

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := authorizedTarget
def currentEvidencePacketId : String := authorityId
def currentBoundedProgramId : String :=
  "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0"
def currentBoundedProgramState : String := "UNINSTALLED"
def currentTargetPhase : String := "PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF"
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_authorizes_only_positive_principle_program_preparation :
    currentLiveTarget =
      "prepare_toe_positive_native_gravitational_principle_derivation_bounded_program_v0" := by
  rfl

theorem positive_principle_program_is_not_installed_or_opened :
    currentBoundedProgramState = "UNINSTALLED" ∧
    currentTargetPhase = "PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED" ∧
    currentBoundedAttemptNumber = 0 ∧ proposalPreparationAuthorized = true ∧
    programInstalled = false ∧ scientificStageOpened = false ∧
    principleInventoryExecuted = false ∧
    nativeGravitationalPrincipleSelectedOrDerived = false ∧
    gravitationalActionSelectedConstructedOrVaried = false ∧
    gravitationalCalculationExecuted = false ∧ evidencePromoted = false ∧
    scientificSuccessorAuthorized = false ∧
    ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout.mandatoryExitCompleted = true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
