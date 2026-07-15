import ToeFormal.Derivation.DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCanonicalExecutionV2

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
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCanonicalExecutionV2.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCanonicalExecutionV2.packetId

theorem current_target_points_to_independent_canonical_result_review :
    currentLiveTarget =
      "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v2_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
