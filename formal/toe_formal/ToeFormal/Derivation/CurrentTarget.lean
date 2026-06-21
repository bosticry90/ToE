import ToeFormal.Derivation.ToeNativeARouteSelectionAfterVacuumU1Variation

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
  ToeNativeARouteSelectionAfterVacuumU1Variation.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeARouteSelectionAfterVacuumU1Variation.packetId

theorem current_target_points_to_a_stress_energy_route_after_vacuum_u1_selector :
    currentLiveTarget =
      "prepare_toe_native_A_stress_energy_route_under_selected_u1_policy" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
