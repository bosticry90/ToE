import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0
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

open ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0.authorizedTarget

def currentEvidencePacketId : String :=
  ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0.authorityId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"

def currentBoundedProgramState : String := "UNINSTALLED"

def currentTargetPhase : String :=
  "PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED"

def currentBoundedAttemptNumber : Nat := 0

def lastClosedBoundedSemanticStage : String :=
  "NATIVE_FRONTIER_DECISION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_authorizes_only_gravitational_survey_proposal_preparation :
    currentLiveTarget =
      "prepare_toe_native_gravitational_requirements_and_candidate_action_family_survey_bounded_program_v0" := by
  rfl

theorem gravitational_survey_program_is_not_installed_or_opened :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "UNINSTALLED" ∧
    currentTargetPhase =
      "PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED" ∧
    currentBoundedAttemptNumber = 0 ∧
    lastClosedBoundedSemanticStage =
      "NATIVE_FRONTIER_DECISION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    proposalPreparationAuthorized = true ∧
    programInstalled = false ∧
    scientificStageOpened = false ∧
    compatibilityCellsAdjudicated = false ∧
    gravitationalActionSelected = false ∧
    evidencePromoted = false ∧
    scientificSuccessorAuthorized = false ∧
    ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout.mandatoryExitCompleted =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
