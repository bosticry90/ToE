import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout
import ToeFormal.Derivation.ToePositiveGravitationalPrincipleSourceInventoryAttemptOpen
import ToeFormal.Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationResultReviewV0
import ToeFormal.Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToePositiveGravitationalPrincipleSourceInventoryAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := scientificTarget
def currentEvidencePacketId : String := eventId
def currentBoundedProgramId : String :=
  "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0"
def currentBoundedProgramState : String := "OPEN"
def currentTargetPhase : String := "STAGE_1_SCIENTIFIC_ATTEMPT_OPEN"
def currentBoundedAttemptNumber : Nat := 1
def lastClosedBoundedSemanticStage : String := "NONE_IN_CURRENT_PROGRAM"
def lastBoundedTerminalResult : String := "NONE"

theorem current_target_records_open_positive_principle_source_inventory :
    currentLiveTarget =
      "inventory_toe_positive_native_gravitational_principle_sources_v0" := by
  rfl

theorem positive_principle_source_inventory_is_open_without_result :
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase = "STAGE_1_SCIENTIFIC_ATTEMPT_OPEN" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage = "NONE_IN_CURRENT_PROGRAM" ∧
    lastBoundedTerminalResult = "NONE" ∧
    Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0.programInstalled =
      true ∧
    Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0.programOpened =
      false ∧
    Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationResultReviewV0.installationAccepted =
      true ∧
    programOpen = true ∧ scientificResultCreated = false ∧
    principleSourceStatementsInventoried = 0 ∧
    principleSelectedOrDerived = false ∧
    gravitationalVariablesSelected = false ∧
    actionClassSelected = false ∧
    gravitationalActionConstructedOrSelected = false ∧
    gravitationalCalculationStarted = false ∧ evidencePromoted = false ∧
    stageTwoAuthorized = false ∧
    ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout.mandatoryExitCompleted =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
