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

open ToeRepositoryWideNativeHypothesisClaimExtractionResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeRepositoryWideNativeHypothesisClaimExtractionResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeRepositoryWideNativeHypothesisClaimExtractionResult.resultId

def currentBoundedProgramId : String :=
  ToeRepositoryWideNativeHypothesisClaimExtractionResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_3_CLOSED_PASSED_STAGE_4_SELECTED_NOT_AUTHORIZED_NOT_OPENED"

def currentBoundedAttemptNumber : Nat :=
  ToeRepositoryWideNativeHypothesisClaimExtractionResult.attemptSequenceNumber

def currentBoundedSemanticStage : String :=
  ToeRepositoryWideNativeHypothesisClaimExtractionResult.semanticStageId

def lastClosedBoundedSemanticStage : String :=
  "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_reconciliation_without_opening_it :
    currentLiveTarget =
      "reconcile_toe_current_native_hypothesis_evidence_v0" := by
  rfl

theorem claim_extraction_stage_is_closed_after_bounded_result :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_3_CLOSED_PASSED_STAGE_4_SELECTED_NOT_AUTHORIZED_NOT_OPENED" ∧
    currentBoundedAttemptNumber = 3 ∧
    currentBoundedSemanticStage =
      "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION" ∧
    lastClosedBoundedSemanticStage =
      "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    sourceBoundClaimsExtracted = true ∧
    scientificClaimsAdjudicated = false ∧
    evidencePromoted = false ∧
    repositoryClaimExhaustionEstablished = false ∧
    nativeFrontierSelected = false ∧
    stageFourAuthorized = false ∧
    stageFourOpened = false ∧
    ToeNativeHypothesisSourceLineageReconstructionResult.documentaryLineageResultProduced =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
