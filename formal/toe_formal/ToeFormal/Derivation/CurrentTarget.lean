import ToeFormal.Derivation.DiracMaxwell3p1To1p1ReductionConsistencyPacketResultReview

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
  DiracMaxwell3p1To1p1ReductionConsistencyPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwell3p1To1p1ReductionConsistencyPacketResultReview.reviewId

theorem current_target_points_to_post_reduction_blocked_route_decision_v0 :
    currentLiveTarget =
      "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
