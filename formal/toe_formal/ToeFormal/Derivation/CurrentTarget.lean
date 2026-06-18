import ToeFormal.Derivation.QFTGRProvisionalScalarClassicalSourceRouteWitnessCloseout

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
  QFTGRProvisionalScalarClassicalSourceRouteWitnessCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRProvisionalScalarClassicalSourceRouteWitnessCloseout.packetId

theorem current_target_points_to_toe_native_matter_sector_definition_packet :
    currentLiveTarget =
      "prepare_toe_native_matter_sector_definition_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
