import ToeFormal.Derivation.MaxwellDiracUnitObjectFoundationPacketResultReview

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
  MaxwellDiracUnitObjectFoundationPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  MaxwellDiracUnitObjectFoundationPacketResultReview.reviewId

theorem current_target_points_to_dirac_maxwell_reduction_consistency_v0 :
    currentLiveTarget =
      "prepare_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
