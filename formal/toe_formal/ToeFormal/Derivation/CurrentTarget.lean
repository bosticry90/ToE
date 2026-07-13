import ToeFormal.Derivation.PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV1ResultReview

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
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV1ResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV1ResultReview.reviewId

theorem current_target_points_to_versioned_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v2 :
    currentLiveTarget =
      "prepare_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet_v2" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
