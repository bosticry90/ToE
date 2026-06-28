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
      "prepare_psi_A_interaction_exchange_theorem_linkage_chain_closeout" := by
  rfl

end CurrentAuthority
end Release
end ToeFormal
