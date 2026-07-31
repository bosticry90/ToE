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

open ToeNativeHypothesisSourceLineageReconstructionResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeNativeHypothesisSourceLineageReconstructionResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeHypothesisSourceLineageReconstructionResult.reviewId

def currentBoundedProgramId : String :=
  ToeNativeHypothesisSourceLineageReconstructionResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_2_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_3_AUTHORITY"

def currentBoundedAttemptNumber : Nat :=
  ToeNativeHypothesisSourceLineageReconstructionResult.attemptSequenceNumber

def currentBoundedSemanticStage : String :=
  ToeNativeHypothesisSourceLineageReconstructionResult.semanticStageId

def lastClosedBoundedSemanticStage : String :=
  "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_unopened_claim_extraction_stage :
    currentLiveTarget =
      "extract_and_classify_toe_repository_wide_native_hypothesis_claims_v0" := by
  rfl

theorem source_lineage_stage_is_closed_passed_without_claim_extraction :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_2_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_3_AUTHORITY" ∧
    currentBoundedAttemptNumber = 2 ∧
    currentBoundedSemanticStage =
      "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION" ∧
    lastClosedBoundedSemanticStage =
      "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    documentaryLineageResultProduced = true ∧
    scientificClaimsExtracted = false ∧
    scientificClaimsAdjudicated = false ∧
    evidencePromoted = false ∧
    nativeFrontierSelected = false ∧
    stageThreeOpened = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
