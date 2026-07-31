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

open ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout.executionTarget

def currentEvidencePacketId : String :=
  ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout.resultId

def currentBoundedProgramId : String :=
  ToeRepositoryWideNativeHypothesisEvidenceCensusV0BoundedCloseout.programId

def currentBoundedProgramState : String := "TERMINAL"

def currentTargetPhase : String :=
  "PROGRAM_CLOSED_AFTER_MANDATORY_EXIT"

def currentBoundedAttemptNumber : Nat := 5

def lastClosedBoundedSemanticStage : String :=
  "NATIVE_FRONTIER_DECISION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_completed_census_mandatory_exit :
    currentLiveTarget =
      "close_toe_repository_wide_native_hypothesis_evidence_census_v0_after_bounded_result_v0" := by
  rfl

theorem repository_wide_census_is_terminal_without_successor_authority :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "TERMINAL" ∧
    currentTargetPhase =
      "PROGRAM_CLOSED_AFTER_MANDATORY_EXIT" ∧
    currentBoundedAttemptNumber = 5 ∧
    lastClosedBoundedSemanticStage =
      "NATIVE_FRONTIER_DECISION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    mandatoryExitSelected = true ∧
    mandatoryExitCompleted = true ∧
    allAttemptsPassed = true ∧
    boundedReviewStatus = "COMPLETE_FOR_THE_BOUNDED_REVIEW" ∧
    repositoryClaimExhaustionEstablished = false ∧
    canonicalEvidencePromoted = false ∧
    candidateGravitationalActionSelected = false ∧
    nativeGravitationalActionEstablished = false ∧
    gravitationalSurveyAuthorized = false ∧
    gravitationalSurveyOpened = false ∧
    automaticSuccessorSelected = false ∧
    successorProgramAuthorized = false ∧
    successorProgramOpened = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
