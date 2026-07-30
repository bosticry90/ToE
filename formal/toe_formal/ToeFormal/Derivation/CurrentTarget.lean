import ToeFormal.Derivation.ToeRepositoryWideNativeHypothesisSourceCensusResult

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeRepositoryWideNativeHypothesisSourceCensusResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeRepositoryWideNativeHypothesisSourceCensusResult.reviewId

def currentBoundedProgramId : String :=
  ToeRepositoryWideNativeHypothesisSourceCensusResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_1_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_2_AUTHORITY"

def currentBoundedAttemptNumber : Nat :=
  ToeRepositoryWideNativeHypothesisSourceCensusResult.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "REPOSITORY_WIDE_SOURCE_CENSUS"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_unopened_source_lineage_stage :
    currentLiveTarget =
      "reconstruct_toe_native_hypothesis_source_lineages_v0" := by
  rfl

theorem repository_wide_source_census_is_closed_passed :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_1_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_2_AUTHORITY" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage = "REPOSITORY_WIDE_SOURCE_CENSUS" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeRepositoryWideNativeHypothesisSourceCensusResult.claimExtractionPerformed =
      false ∧
    ToeRepositoryWideNativeHypothesisSourceCensusResult.lineageConclusionProduced =
      false ∧
    ToeRepositoryWideNativeHypothesisSourceCensusResult.stageTwoOpened =
      false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
