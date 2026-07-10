import ToeFormal.Derivation.ScalarStressEnergyCovariantDivergenceIdentityConformalBackgroundCalculationExecution

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
  ScalarStressEnergyCovariantDivergenceIdentityConformalBackgroundCalculationExecution.selectedNextTarget

def currentEvidencePacketId : String :=
  ScalarStressEnergyCovariantDivergenceIdentityConformalBackgroundCalculationExecution.executionId

theorem current_target_points_to_conformal_background_result_review :
    currentLiveTarget =
      "review_calc_scalar_stress_energy_covariant_divergence_identity_conformal_background_v0_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
