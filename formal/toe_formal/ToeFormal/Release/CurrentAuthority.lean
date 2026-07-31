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

open Derivation.ToePostCensusNativeFrontierDecisionAttemptOpen

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

theorem current_authority_tracks_open_frontier_decision_stage :
    currentTarget =
      "select_toe_native_frontier_after_repository_wide_evidence_census_v0" := by
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

theorem census_program_stage_5_is_open_without_a_frontier_result :
    boundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_5_OPEN_AWAITING_POST_CENSUS_NATIVE_FRONTIER_DECISION_RESULT" ∧
    boundedAttemptNumber = 5 ∧
    Derivation.ToeRepositoryWideNativeHypothesisClaimExtractionResult.sourceBoundClaimsExtracted =
      true ∧
    Derivation.ToeCurrentNativeHypothesisEvidenceReconciliationResult.claimReconciliationComplete =
      true ∧
    Derivation.ToeCurrentNativeHypothesisEvidenceReconciliationResult.nativeHypothesisGraphProduced =
      true ∧
    frontierRankingPerformed = false ∧
    frontierRankingResultProduced = false ∧
    nativeFrontierSelected = false ∧
    scientificClaimAdjudicated = false ∧
    canonicalEvidencePromoted = false ∧
    representationActionOrSeamSelected = false ∧
    successorProgramAuthorizedOrOpened = false ∧
    mandatoryExitExecuted = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
