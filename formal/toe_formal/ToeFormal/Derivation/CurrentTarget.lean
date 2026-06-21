import ToeFormal.Derivation.ToeNativeASurfaceVariationAndSourceRoutePacket

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
  ToeNativeASurfaceVariationAndSourceRoutePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeASurfaceVariationAndSourceRoutePacket.packetId

theorem current_target_points_to_a_surface_route_result_review :
    currentLiveTarget =
      "review_toe_native_A_surface_variation_and_source_route_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
