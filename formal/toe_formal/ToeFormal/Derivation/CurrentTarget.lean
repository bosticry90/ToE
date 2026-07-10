import ToeFormal.Derivation.ScalarStressEnergyCovariantDivergenceIdentityHigherDimensionalCurvedBackgroundCalculationExecution

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
  ScalarStressEnergyCovariantDivergenceIdentityHigherDimensionalCurvedBackgroundCalculationExecution.selectedNextTarget

def currentEvidencePacketId : String :=
  ScalarStressEnergyCovariantDivergenceIdentityHigherDimensionalCurvedBackgroundCalculationExecution.executionId

theorem current_target_points_to_higher_dimensional_curved_background_result_review :
    currentLiveTarget =
      "review_calc_scalar_stress_energy_covariant_divergence_identity_higher_dimensional_curved_background_v0_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
