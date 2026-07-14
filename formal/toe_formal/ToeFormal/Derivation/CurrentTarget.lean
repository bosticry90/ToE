import ToeFormal.Derivation.PostDiracMaxwellFullZeroModeCanonicalResultRouteDecisionPacketResultReview

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
  PostDiracMaxwellFullZeroModeCanonicalResultRouteDecisionPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PostDiracMaxwellFullZeroModeCanonicalResultRouteDecisionPacketResultReview.reviewId

theorem current_target_points_to_descendant_necessity_and_robustness_v0 :
    currentLiveTarget =
      "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
