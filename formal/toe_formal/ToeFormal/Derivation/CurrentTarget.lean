import ToeFormal.Derivation.ToeNativeMatterSectorDefinitionPacket

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
  ToeNativeMatterSectorDefinitionPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeMatterSectorDefinitionPacket.packetId

theorem current_target_points_to_toe_native_matter_sector_definition_packet_review :
    currentLiveTarget =
      "review_toe_native_matter_sector_definition_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
