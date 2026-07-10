import ToeFormal.Derivation.ScalarStressEnergyDivergenceIdentityMinkowskiCalculationExecution

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
  ScalarStressEnergyDivergenceIdentityMinkowskiCalculationExecution.selectedNextTarget

def currentEvidencePacketId : String :=
  ScalarStressEnergyDivergenceIdentityMinkowskiCalculationExecution.executionId

theorem current_target_points_to_minkowski_result_review :
    currentLiveTarget =
      "review_calc_scalar_stress_energy_divergence_identity_minkowski_v0_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
