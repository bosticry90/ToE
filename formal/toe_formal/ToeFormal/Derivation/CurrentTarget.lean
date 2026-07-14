import ToeFormal.Derivation.DiracMaxwellFullZeroModeCanonicalSimulationResultReview

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
  DiracMaxwellFullZeroModeCanonicalSimulationResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeCanonicalSimulationResultReview.reviewId

theorem current_target_points_to_post_result_route_decision_v0 :
    currentLiveTarget =
      "prepare_post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
