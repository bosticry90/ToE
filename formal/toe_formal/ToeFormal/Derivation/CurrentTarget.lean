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

open ToePostCensusNativeFrontierDecisionAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToePostCensusNativeFrontierDecisionAttemptOpen.target

def currentEvidencePacketId : String :=
  ToePostCensusNativeFrontierDecisionAttemptOpen.evidenceId

def currentBoundedProgramId : String :=
  ToePostCensusNativeFrontierDecisionAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_5_OPEN_AWAITING_POST_CENSUS_NATIVE_FRONTIER_DECISION_RESULT"

def currentBoundedAttemptNumber : Nat :=
  ToePostCensusNativeFrontierDecisionAttemptOpen.attemptSequenceNumber

def currentBoundedSemanticStage : String :=
  ToePostCensusNativeFrontierDecisionAttemptOpen.semanticStageId

def lastClosedBoundedSemanticStage : String :=
  "CURRENT_HYPOTHESIS_RECONCILIATION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_opens_bounded_frontier_decision :
    currentLiveTarget =
      "select_toe_native_frontier_after_repository_wide_evidence_census_v0" := by
  rfl

theorem frontier_decision_stage_is_open_after_reconciliation_close :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_5_OPEN_AWAITING_POST_CENSUS_NATIVE_FRONTIER_DECISION_RESULT" ∧
    currentBoundedAttemptNumber = 5 ∧
    currentBoundedSemanticStage =
      "NATIVE_FRONTIER_DECISION" ∧
    lastClosedBoundedSemanticStage =
      "CURRENT_HYPOTHESIS_RECONCILIATION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeRepositoryWideNativeHypothesisClaimExtractionResult.sourceBoundClaimsExtracted =
      true ∧
    ToeCurrentNativeHypothesisEvidenceReconciliationResult.claimReconciliationComplete =
      true ∧
    ToeCurrentNativeHypothesisEvidenceReconciliationResult.nativeHypothesisGraphProduced =
      true ∧
    frontierRankingPerformed = false ∧
    frontierRankingResultProduced = false ∧
    nativeFrontierSelected = false ∧
    scientificClaimAdjudicated = false ∧
    canonicalEvidencePromoted = false ∧
    representationActionOrSeamSelected = false ∧
    successorProgramAuthorizedOrOpened = false ∧
    mandatoryExitExecuted = false ∧
    ToeNativeHypothesisSourceLineageReconstructionResult.documentaryLineageResultProduced =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
