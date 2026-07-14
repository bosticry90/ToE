import ToeFormal.Derivation.DiracMaxwellFullZeroModeNonAuthoritativePilotResultReview

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
  DiracMaxwellFullZeroModeNonAuthoritativePilotResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeNonAuthoritativePilotResultReview.reviewId

theorem current_target_points_to_pilot_implementation_repair_v0 :
    currentLiveTarget =
      "prepare_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
