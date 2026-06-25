import ToeFormal.Derivation.ToeNativePsiAU1StressEnergyAndExchangeObligationPacket

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
  ToeNativePsiAU1StressEnergyAndExchangeObligationPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePsiAU1StressEnergyAndExchangeObligationPacket.packetId

theorem current_target_points_to_psi_a_u1_stress_energy_definition_policy_packet :
    currentLiveTarget =
      "prepare_toe_native_psi_A_u1_stress_energy_definition_policy_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
