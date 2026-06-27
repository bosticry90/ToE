import ToeFormal.Derivation.CurrentTarget

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

theorem current_authority_tracks_current_target :
    currentTarget =
      "prepare_master_action_ck_family_gap_review_after_phi_A_and_psi_A" := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
