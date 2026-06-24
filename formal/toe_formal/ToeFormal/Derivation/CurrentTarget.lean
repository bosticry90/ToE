import ToeFormal.Derivation.ToeNativeATransportConsistencyCKAdmissibilityRuleCloseout

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
  ToeNativeATransportConsistencyCKAdmissibilityRuleCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeATransportConsistencyCKAdmissibilityRuleCloseout.packetId

theorem current_target_points_to_a_ck_source_bridge_transport_synthesis_packet :
    currentLiveTarget =
      "prepare_toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
