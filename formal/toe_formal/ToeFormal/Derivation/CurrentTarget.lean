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

open ToeCurrentNativeHypothesisEvidenceReconciliationResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeCurrentNativeHypothesisEvidenceReconciliationResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeCurrentNativeHypothesisEvidenceReconciliationResult.resultId

def currentBoundedProgramId : String :=
  ToeCurrentNativeHypothesisEvidenceReconciliationResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_4_CLOSED_PASSED_WITH_CONFLICTS_STAGE_5_SELECTED_NOT_AUTHORIZED_NOT_OPENED"

def currentBoundedAttemptNumber : Nat :=
  ToeCurrentNativeHypothesisEvidenceReconciliationResult.attemptSequenceNumber

def currentBoundedSemanticStage : String :=
  ToeCurrentNativeHypothesisEvidenceReconciliationResult.semanticStageId

def lastClosedBoundedSemanticStage : String :=
  "CURRENT_HYPOTHESIS_RECONCILIATION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_frontier_decision_without_opening_it :
    currentLiveTarget =
      "select_toe_native_frontier_after_repository_wide_evidence_census_v0" := by
  rfl

theorem reconciliation_stage_is_closed_after_bounded_result :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_4_CLOSED_PASSED_WITH_CONFLICTS_STAGE_5_SELECTED_NOT_AUTHORIZED_NOT_OPENED" ∧
    currentBoundedAttemptNumber = 4 ∧
    currentBoundedSemanticStage =
      "CURRENT_HYPOTHESIS_RECONCILIATION" ∧
    lastClosedBoundedSemanticStage =
      "CURRENT_HYPOTHESIS_RECONCILIATION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeRepositoryWideNativeHypothesisClaimExtractionResult.sourceBoundClaimsExtracted =
      true ∧
    claimReconciliationComplete = true ∧
    nativeHypothesisGraphProduced = true ∧
    conflictsPreserved = true ∧
    scientificClaimsAdjudicated = false ∧
    canonicalEvidencePromoted = false ∧
    nativeFrontierSelected = false ∧
    repositoryClaimExhaustionEstablished = false ∧
    stageFiveAuthorized = false ∧
    stageFiveOpened = false ∧
    ToeNativeHypothesisSourceLineageReconstructionResult.documentaryLineageResultProduced =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
