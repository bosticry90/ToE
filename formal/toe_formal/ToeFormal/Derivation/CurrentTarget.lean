import ToeFormal.Derivation.PhiTransportConsistencyCKAdmissibilityRuleCloseout

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
  PhiTransportConsistencyCKAdmissibilityRuleCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiTransportConsistencyCKAdmissibilityRuleCloseout.packetId

theorem current_target_points_to_phi_ck_source_bridge_transport_family_synthesis :
    currentLiveTarget =
      "prepare_phi_ck_source_bridge_transport_rule_family_synthesis_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
