import ToeFormal.Derivation.ToePostCensusNativeFrontierDecisionResult
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

open ToePostCensusNativeFrontierDecisionResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToePostCensusNativeFrontierDecisionResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToePostCensusNativeFrontierDecisionResult.resultId

def currentBoundedProgramId : String :=
  ToePostCensusNativeFrontierDecisionResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_5_CLOSED_PASSED_FRONTIER_SELECTED_AFTER_ONE_PREREQUISITE_MANDATORY_EXIT_SELECTED_NOT_EXECUTED"

def currentBoundedAttemptNumber : Nat :=
  ToePostCensusNativeFrontierDecisionResult.attemptSequenceNumber

def currentBoundedSemanticStage : String :=
  ToePostCensusNativeFrontierDecisionResult.semanticStageId

def lastClosedBoundedSemanticStage : String :=
  "NATIVE_FRONTIER_DECISION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_exact_census_mandatory_exit :
    currentLiveTarget =
      "close_toe_repository_wide_native_hypothesis_evidence_census_v0_after_bounded_result_v0" := by
  rfl

theorem frontier_decision_stage_is_closed_without_successor_authority :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_5_CLOSED_PASSED_FRONTIER_SELECTED_AFTER_ONE_PREREQUISITE_MANDATORY_EXIT_SELECTED_NOT_EXECUTED" ∧
    currentBoundedAttemptNumber = 5 ∧
    currentBoundedSemanticStage =
      "NATIVE_FRONTIER_DECISION" ∧
    lastClosedBoundedSemanticStage =
      "NATIVE_FRONTIER_DECISION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeRepositoryWideNativeHypothesisClaimExtractionResult.sourceBoundClaimsExtracted =
      true ∧
    ToeCurrentNativeHypothesisEvidenceReconciliationResult.claimReconciliationComplete =
      true ∧
    ToeCurrentNativeHypothesisEvidenceReconciliationResult.nativeHypothesisGraphProduced =
      true ∧
    frontierRankingComplete = true ∧
    nativeFrontierSelected = true ∧
    selectedFamilyId = "GRAVITY_SECTOR" ∧
    selectedFrontierIsResearchTargetOnly = true ∧
    scientificClaimTruthAdjudicated = false ∧
    canonicalEvidencePromoted = false ∧
    fieldActionOrSeamSelected = false ∧
    proposedFutureTargetAuthorized = false ∧
    proposedFutureTargetOpened = false ∧
    mandatoryExitSelected = true ∧
    mandatoryExitExecuted = false ∧
    ToeNativeHypothesisSourceLineageReconstructionResult.documentaryLineageResultProduced =
      true := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
