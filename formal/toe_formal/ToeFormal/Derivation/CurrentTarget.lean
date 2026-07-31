import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0
import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyBoundedProgramPreparationResultReview
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

open ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyBoundedProgramPreparationResultReview

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyBoundedProgramPreparationResultReview.scientificTarget

def currentEvidencePacketId : String :=
  ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyBoundedProgramPreparationResultReview.resultId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"

def currentBoundedProgramState : String := "UNINSTALLED"

def currentTargetPhase : String :=
  "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"

def currentBoundedAttemptNumber : Nat := 0

def lastClosedBoundedSemanticStage : String :=
  "NATIVE_FRONTIER_DECISION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_prepared_gravitational_survey_program_proposal :
    currentLiveTarget =
      "prepare_toe_native_gravitational_requirements_and_candidate_action_family_survey_bounded_program_v0" := by
  rfl

theorem gravitational_survey_program_proposal_is_reviewed_but_uninstalled :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "UNINSTALLED" ∧
    currentTargetPhase =
      "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY" ∧
    currentBoundedAttemptNumber = 0 ∧
    lastClosedBoundedSemanticStage =
      "NATIVE_FRONTIER_DECISION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    proposalPrepared = true ∧
    independentReviewAccepted = true ∧
    programInstalled = false ∧
    scientificStageOpened = false ∧
    compatibilitySurveyExecuted = false ∧
    gravitationalActionSelected = false ∧
    evidencePromoted = false ∧
    automaticSuccessorSelected = false ∧
    closedV2MatrixPopulationPermitted = false ∧
    ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout.mandatoryExitCompleted =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
