import ToeFormal.Derivation.DiracMaxwellFullZeroModeNonAuthoritativePilotV1ResultReview

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
  DiracMaxwellFullZeroModeNonAuthoritativePilotV1ResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeNonAuthoritativePilotV1ResultReview.reviewId

theorem current_target_points_to_canonical_parameter_freeze_v0 :
    currentLiveTarget =
      "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
