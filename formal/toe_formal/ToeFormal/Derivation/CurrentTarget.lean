import ToeFormal.Derivation.PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacket

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
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacket.packetId

theorem current_target_points_to_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_review :
    currentLiveTarget =
      "review_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
