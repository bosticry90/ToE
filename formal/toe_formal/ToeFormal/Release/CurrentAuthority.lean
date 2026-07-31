import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0

/-
Release-facing current-authority aggregate for tiered validation. It is a small
build target for authority-surface synchronization checks and intentionally
does not replace the full ToeFormal release aggregate.
-/

namespace ToeFormal
namespace Release
namespace CurrentAuthority

open Derivation.ToePostCensusNativeFrontierDecisionResult

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"

def currentTarget : String :=
  Derivation.CurrentTarget.currentLiveTarget

def currentEvidencePacketId : String :=
  Derivation.CurrentTarget.currentEvidencePacketId

def boundedProgramId : String :=
  Derivation.CurrentTarget.currentBoundedProgramId

def boundedProgramState : String :=
  Derivation.CurrentTarget.currentBoundedProgramState

def currentTargetPhase : String :=
  Derivation.CurrentTarget.currentTargetPhase

def boundedAttemptNumber : Nat :=
  Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_selected_census_mandatory_exit :
    currentTarget =
      "close_toe_repository_wide_native_hypothesis_evidence_census_v0_after_bounded_result_v0" := by
  native_decide

theorem bounded_program_governance_installation_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated =
      false := by
  native_decide

theorem bounded_program_governance_review_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem census_program_stage_5_is_closed_without_successor_authority :
    boundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    boundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_5_CLOSED_PASSED_FRONTIER_SELECTED_AFTER_ONE_PREREQUISITE_MANDATORY_EXIT_SELECTED_NOT_EXECUTED" ∧
    boundedAttemptNumber = 5 ∧
    Derivation.ToeRepositoryWideNativeHypothesisClaimExtractionResult.sourceBoundClaimsExtracted =
      true ∧
    Derivation.ToeCurrentNativeHypothesisEvidenceReconciliationResult.claimReconciliationComplete =
      true ∧
    Derivation.ToeCurrentNativeHypothesisEvidenceReconciliationResult.nativeHypothesisGraphProduced =
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
    mandatoryExitExecuted = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
