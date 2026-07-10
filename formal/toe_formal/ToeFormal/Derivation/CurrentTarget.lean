import ToeFormal.Derivation.BoundedCurvedSpaceScalarQFTGRSourceContractRetestGuardrailPacket

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
  BoundedCurvedSpaceScalarQFTGRSourceContractRetestGuardrailPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  BoundedCurvedSpaceScalarQFTGRSourceContractRetestGuardrailPacket.packetId

theorem current_target_points_to_fixed_conformal_background_execution :
    currentLiveTarget =
      "execute_calc_scalar_stress_energy_covariant_divergence_identity_conformal_background_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
