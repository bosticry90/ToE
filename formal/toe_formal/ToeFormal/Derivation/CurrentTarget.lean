import ToeFormal.Derivation.ToeNativeMatterSectorDefinitionPacketResultReview

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
  ToeNativeMatterSectorDefinitionPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeMatterSectorDefinitionPacketResultReview.packetId

theorem current_target_points_to_toe_native_matter_sector_calculation_route_selection :
    currentLiveTarget =
      "select_toe_native_matter_sector_calculation_route" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
