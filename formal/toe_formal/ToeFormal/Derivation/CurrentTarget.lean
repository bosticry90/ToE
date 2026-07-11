import ToeFormal.Derivation.PillarSeamUnitMappingLedgerGuardrailPacket

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
  PillarSeamUnitMappingLedgerGuardrailPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  PillarSeamUnitMappingLedgerGuardrailPacket.packetId

theorem current_target_points_to_pillar_seam_unit_mapping_ledger_execution :
    currentLiveTarget =
      "execute_pillar_seam_unit_mapping_ledger_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
