import ToeFormal.Derivation.ScalarStressEnergyCovariantDivergenceIdentityConformalBackgroundCalculationResultReview

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
  ScalarStressEnergyCovariantDivergenceIdentityConformalBackgroundCalculationResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ScalarStressEnergyCovariantDivergenceIdentityConformalBackgroundCalculationResultReview.reviewId

theorem current_target_points_to_nonzero_curvature_guardrail :
    currentLiveTarget =
      "prepare_scalar_stress_energy_covariant_divergence_identity_nonzero_curvature_background_guardrail_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
