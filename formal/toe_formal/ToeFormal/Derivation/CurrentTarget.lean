import ToeFormal.Derivation.DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessNonAuthoritativePilotV1ResultReview

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
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessNonAuthoritativePilotV1ResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessNonAuthoritativePilotV1ResultReview.reviewId

theorem current_target_points_to_calibration_and_full_run_freeze_preparation :
    currentLiveTarget =
      "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
