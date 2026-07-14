import ToeFormal.Derivation.DiracMaxwellFullZeroModePilotImplementationRepairPacketResultReview

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
  DiracMaxwellFullZeroModePilotImplementationRepairPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModePilotImplementationRepairPacketResultReview.reviewId

theorem current_target_points_to_non_authoritative_pilot_v1 :
    currentLiveTarget =
      "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
