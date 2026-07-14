import ToeFormal.Derivation.PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV2ResultReview

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
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV2ResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV2ResultReview.reviewId

theorem current_target_points_to_first_unit_selector_v0 :
    currentLiveTarget =
      "prepare_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
