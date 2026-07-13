import ToeFormal.Derivation.PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketResultReview

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
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketResultReview.reviewId

theorem current_target_points_to_versioned_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_correction :
    currentLiveTarget =
      "prepare_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet_v1" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
