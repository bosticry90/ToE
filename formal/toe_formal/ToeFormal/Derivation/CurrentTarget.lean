import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0
import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyBoundedProgramPreparationResultReview
import ToeFormal.Derivation.ToeNativeGravitationalRequirementInventoryAttemptOpen
import ToeFormal.Release.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationV0
import ToeFormal.Release.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationResultReviewV0
import ToeFormal.Derivation.ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout
import ToeFormal.Derivation.ToePostCensusNativeFrontierDecisionAttemptOpen
import ToeFormal.Derivation.ToeCurrentNativeHypothesisEvidenceReconciliationResult
import ToeFormal.Derivation.ToeRepositoryWideNativeHypothesisClaimExtractionResult
import ToeFormal.Derivation.ToeNativeHypothesisSourceLineageReconstructionResult
import ToeFormal.Derivation.ToeRepositoryWideNativeHypothesisSourceCensusResult

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeNativeGravitationalRequirementInventoryAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeNativeGravitationalRequirementInventoryAttemptOpen.scientificTarget

def currentEvidencePacketId : String :=
  ToeNativeGravitationalRequirementInventoryAttemptOpen.eventId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_1_SCIENTIFIC_ATTEMPT_OPEN"

def currentBoundedAttemptNumber : Nat := 1

def lastClosedBoundedSemanticStage : String :=
  "NONE_IN_CURRENT_PROGRAM"

def lastBoundedTerminalResult : String := "NONE"

theorem current_target_records_open_gravitational_requirement_inventory :
    currentLiveTarget =
      "inventory_toe_native_gravitational_requirements_v0" := by
  rfl

theorem gravitational_requirement_inventory_is_open_without_result :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_1_SCIENTIFIC_ATTEMPT_OPEN" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage =
      "NONE_IN_CURRENT_PROGRAM" ∧
    lastBoundedTerminalResult = "NONE" ∧
    Release.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationV0.programInstalled =
      true ∧
    Release.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationV0.programOpened = false ∧
    Release.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationResultReviewV0.installationAccepted =
      true ∧
    programOpen = true ∧
    scientificResultCreated = false ∧
    requirementRowsAdjudicated = 0 ∧
    actionFamiliesCompared = false ∧
    evidencePromoted = false ∧
    gravitationalActionSelected = false ∧
    nativeGravitationalPrincipleSelected = false ∧
    gravitationalCalculationStarted = false ∧
    stageTwoAuthorized = false ∧
    ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout.mandatoryExitCompleted =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
