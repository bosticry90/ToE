import ToeFormal.Derivation.DiracMaxwellFullZeroModeCanonicalParameterFreezePacketResultReview

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  DiracMaxwellFullZeroModeCanonicalParameterFreezePacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeCanonicalParameterFreezePacketResultReview.reviewId

theorem current_target_points_to_canonical_simulation_v0 :
    currentLiveTarget =
      "execute_dirac_maxwell_full_zero_mode_canonical_simulation_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
