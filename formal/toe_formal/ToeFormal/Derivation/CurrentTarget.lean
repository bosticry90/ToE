import ToeFormal.Derivation.ScalarStressEnergyCovariantDivergenceIdentityMultiBackgroundRobustnessGuardrailPacket

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
  ScalarStressEnergyCovariantDivergenceIdentityMultiBackgroundRobustnessGuardrailPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ScalarStressEnergyCovariantDivergenceIdentityMultiBackgroundRobustnessGuardrailPacket.packetId

theorem current_target_points_to_multi_background_robustness_execution :
    currentLiveTarget =
      "execute_calc_scalar_stress_energy_covariant_divergence_identity_multi_background_robustness_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
