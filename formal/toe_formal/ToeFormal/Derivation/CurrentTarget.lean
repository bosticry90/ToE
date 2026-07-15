import ToeFormal.Derivation.DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV3ResultReview

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
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV3ResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV3ResultReview.reviewId

theorem current_target_points_to_one_time_canonical_execution :
    currentLiveTarget =
      "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v2" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
