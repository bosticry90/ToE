import ToeFormal.Derivation.ToeCurrentNativeHypothesisEvidenceReconciliationAttemptOpen
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

open ToeCurrentNativeHypothesisEvidenceReconciliationAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeCurrentNativeHypothesisEvidenceReconciliationAttemptOpen.target

def currentEvidencePacketId : String :=
  ToeCurrentNativeHypothesisEvidenceReconciliationAttemptOpen.evidenceId

def currentBoundedProgramId : String :=
  ToeCurrentNativeHypothesisEvidenceReconciliationAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_4_OPEN_AWAITING_CURRENT_HYPOTHESIS_RECONCILIATION_RESULT"

def currentBoundedAttemptNumber : Nat :=
  ToeCurrentNativeHypothesisEvidenceReconciliationAttemptOpen.attemptSequenceNumber

def currentBoundedSemanticStage : String :=
  ToeCurrentNativeHypothesisEvidenceReconciliationAttemptOpen.semanticStageId

def lastClosedBoundedSemanticStage : String :=
  "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_is_open_reconciliation_stage :
    currentLiveTarget =
      "reconcile_toe_current_native_hypothesis_evidence_v0" := by
  rfl

theorem reconciliation_stage_is_open_after_claim_extraction_close :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_4_OPEN_AWAITING_CURRENT_HYPOTHESIS_RECONCILIATION_RESULT" ∧
    currentBoundedAttemptNumber = 4 ∧
    currentBoundedSemanticStage =
      "CURRENT_HYPOTHESIS_RECONCILIATION" ∧
    lastClosedBoundedSemanticStage =
      "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeRepositoryWideNativeHypothesisClaimExtractionResult.sourceBoundClaimsExtracted =
      true ∧
    reconciliationPerformed = false ∧
    reconciliationResultProduced = false ∧
    currentHypothesisGraphProduced = false ∧
    scientificClaimAdjudicated = false ∧
    canonicalEvidencePromoted = false ∧
    nativeFrontierSelected = false ∧
    stageFiveOpened = false ∧
    ToeNativeHypothesisSourceLineageReconstructionResult.documentaryLineageResultProduced =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
