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

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"

def currentTarget : String :=
  Derivation.CurrentTarget.currentLiveTarget

def currentEvidencePacketId : String :=
  Derivation.CurrentTarget.currentEvidencePacketId

def boundedProgramId : String :=
  Derivation.CurrentTarget.currentBoundedProgramId

def boundedProgramState : String :=
  Derivation.CurrentTarget.currentBoundedProgramState

def boundedAttemptNumber : Nat :=
  Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_current_target :
    currentTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem bounded_program_governance_does_not_rotate_scientific_authority :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      currentTarget ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated =
      false := by
  native_decide

theorem bounded_program_governance_review_preserves_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      currentTarget := by
  native_decide

theorem bounded_quadratic_stage_one_is_open :
    boundedProgramId = "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0" ∧
    boundedProgramState = "OPEN" ∧
    boundedAttemptNumber = 1 := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
