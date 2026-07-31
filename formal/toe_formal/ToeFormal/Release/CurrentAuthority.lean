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

open Derivation.ToeRepositoryWideNativeHypothesisClaimExtractionAttemptOpen

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

theorem current_authority_tracks_open_claim_extraction_stage :
    currentTarget =
      "extract_and_classify_toe_repository_wide_native_hypothesis_claims_v0" := by
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

theorem census_program_stage_3_is_open :
    boundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_3_OPEN_AWAITING_NATIVE_CLAIM_EXTRACTION_RESULT" ∧
    boundedAttemptNumber = 3 ∧
    scientificOutputPresent = false ∧
    claimExtractionPerformed = false ∧
    claimExtractionResultProduced = false ∧
    scientificClaimAdjudicated = false ∧
    evidencePromoted = false ∧
    reconciliationPerformed = false ∧
    nativeFrontierSelected = false ∧
    stageFourOpened = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
