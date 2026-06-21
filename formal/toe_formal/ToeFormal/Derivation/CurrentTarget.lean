import ToeFormal.Derivation.ToeNativeAStressEnergyRouteUnderSelectedU1PolicyPacket

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
  ToeNativeAStressEnergyRouteUnderSelectedU1PolicyPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeAStressEnergyRouteUnderSelectedU1PolicyPacket.packetId

theorem current_target_points_to_a_stress_energy_route_result_review :
    currentLiveTarget =
      "review_toe_native_A_stress_energy_route_under_selected_u1_policy_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
