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
      "prepare_qft_gr_quadratic_hyperbolicity_admissible_source_and_frozen_theory_packet_v0" := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
