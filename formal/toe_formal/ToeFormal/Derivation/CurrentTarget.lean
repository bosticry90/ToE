import ToeFormal.Derivation.ToeNativePhiSurfaceVariationAndSourceRoutePacket

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
  ToeNativePhiSurfaceVariationAndSourceRoutePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePhiSurfaceVariationAndSourceRoutePacket.packetId

theorem current_target_points_to_toe_native_phi_surface_route_review :
    currentLiveTarget =
      "review_toe_native_phi_surface_variation_and_source_route_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
