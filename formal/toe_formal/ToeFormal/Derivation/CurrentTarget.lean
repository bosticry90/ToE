import ToeFormal.Derivation.PhiCKSourceBridgeTransportRuleFamilySynthesisPacket

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
  PhiCKSourceBridgeTransportRuleFamilySynthesisPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiCKSourceBridgeTransportRuleFamilySynthesisPacket.packetId

theorem current_target_points_to_phi_ck_source_bridge_transport_family_synthesis_review :
    currentLiveTarget =
      "review_phi_ck_source_bridge_transport_rule_family_synthesis_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
