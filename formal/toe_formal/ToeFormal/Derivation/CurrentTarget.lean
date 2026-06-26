import ToeFormal.Derivation.ToeNativePsiAU1TotalStressEnergyConservationRoutePacket

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
  ToeNativePsiAU1TotalStressEnergyConservationRoutePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePsiAU1TotalStressEnergyConservationRoutePacket.packetId

theorem current_target_points_to_psi_a_u1_total_stress_energy_conservation_route_packet_result_review :
    currentLiveTarget =
      "review_toe_native_psi_A_u1_total_stress_energy_conservation_route_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
