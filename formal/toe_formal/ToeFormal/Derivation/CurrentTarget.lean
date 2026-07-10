import ToeFormal.Derivation.ScalarQFTGRSourceContractFlatLimitPretestGuardrailPacket

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
  ScalarQFTGRSourceContractFlatLimitPretestGuardrailPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ScalarQFTGRSourceContractFlatLimitPretestGuardrailPacket.packetId

theorem current_target_points_to_minkowski_execution :
    currentLiveTarget =
      "execute_calc_scalar_stress_energy_divergence_identity_minkowski_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
