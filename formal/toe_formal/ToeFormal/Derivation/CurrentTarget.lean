import ToeFormal.Derivation.ToeRepositoryWideNativeHypothesisClaimExtractionAttemptOpen
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

open ToeRepositoryWideNativeHypothesisClaimExtractionAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeRepositoryWideNativeHypothesisClaimExtractionAttemptOpen.target

def currentEvidencePacketId : String :=
  ToeRepositoryWideNativeHypothesisClaimExtractionAttemptOpen.evidenceId

def currentBoundedProgramId : String :=
  ToeRepositoryWideNativeHypothesisClaimExtractionAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_3_OPEN_AWAITING_NATIVE_CLAIM_EXTRACTION_RESULT"

def currentBoundedAttemptNumber : Nat :=
  ToeRepositoryWideNativeHypothesisClaimExtractionAttemptOpen.attemptSequenceNumber

def currentBoundedSemanticStage : String :=
  ToeRepositoryWideNativeHypothesisClaimExtractionAttemptOpen.semanticStageId

def lastClosedBoundedSemanticStage : String :=
  "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_opens_claim_extraction_stage :
    currentLiveTarget =
      "extract_and_classify_toe_repository_wide_native_hypothesis_claims_v0" := by
  rfl

theorem claim_extraction_stage_is_open_after_lineage_close :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_3_OPEN_AWAITING_NATIVE_CLAIM_EXTRACTION_RESULT" ∧
    currentBoundedAttemptNumber = 3 ∧
    currentBoundedSemanticStage =
      "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION" ∧
    lastClosedBoundedSemanticStage =
      "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    scientificOutputPresent = false ∧
    claimExtractionPerformed = false ∧
    claimExtractionResultProduced = false ∧
    scientificClaimAdjudicated = false ∧
    evidencePromoted = false ∧
    reconciliationPerformed = false ∧
    nativeFrontierSelected = false ∧
    stageFourOpened = false ∧
    ToeNativeHypothesisSourceLineageReconstructionResult.documentaryLineageResultProduced =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
