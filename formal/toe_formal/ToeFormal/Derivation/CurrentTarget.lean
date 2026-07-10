import ToeFormal.Derivation.ScalarStressEnergyCovariantDivergenceIdentityNonzeroCurvatureBackgroundGuardrailPacket

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
  ScalarStressEnergyCovariantDivergenceIdentityNonzeroCurvatureBackgroundGuardrailPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ScalarStressEnergyCovariantDivergenceIdentityNonzeroCurvatureBackgroundGuardrailPacket.packetId

theorem current_target_points_to_nonzero_curvature_execution :
    currentLiveTarget =
      "execute_calc_scalar_stress_energy_covariant_divergence_identity_nonzero_curvature_background_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
