import ToeFormal.Derivation.MasterActionSurfaceSelectionAfterPhiCKTriad

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
  MasterActionSurfaceSelectionAfterPhiCKTriad.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionSurfaceSelectionAfterPhiCKTriad.packetId

theorem current_target_points_to_a_surface_route_packet :
    currentLiveTarget =
      "prepare_toe_native_A_surface_variation_and_source_route_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
