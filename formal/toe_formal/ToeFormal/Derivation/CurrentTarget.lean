import ToeFormal.Derivation.ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisPacket

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
  ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePsiAU1InteractionExchangeRuleFamilySynthesisPacket.packetId

theorem current_target_points_to_psi_a_u1_interaction_exchange_rule_family_synthesis_result_review :
    currentLiveTarget =
      "review_toe_native_psi_A_u1_interaction_exchange_rule_family_synthesis_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
