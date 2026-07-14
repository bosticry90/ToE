import ToeFormal.Derivation.DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessAxisNormalizationRepairPacketResultReview

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
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessAxisNormalizationRepairPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessAxisNormalizationRepairPacketResultReview.reviewId

theorem current_target_points_to_descendant_necessity_and_robustness_guardrail_v1 :
    currentLiveTarget =
      "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v1" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
