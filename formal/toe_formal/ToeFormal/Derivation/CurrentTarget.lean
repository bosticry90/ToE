import ToeFormal.Derivation.PillarSeamUnitMappingLedgerFirstUnitSelectorPacketResultReview

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
  PillarSeamUnitMappingLedgerFirstUnitSelectorPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PillarSeamUnitMappingLedgerFirstUnitSelectorPacketResultReview.reviewId

theorem current_target_points_to_maxwell_dirac_unit_object_foundation_v0 :
    currentLiveTarget =
      "prepare_maxwell_dirac_unit_object_foundation_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
