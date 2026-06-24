import ToeFormal.Derivation.ToeNativeACKSourceBridgeTransportRuleFamilyCloseout

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
  ToeNativeACKSourceBridgeTransportRuleFamilyCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeACKSourceBridgeTransportRuleFamilyCloseout.packetId

theorem current_target_points_to_post_a_ck_triad_interaction_selector :
    currentLiveTarget =
      "select_next_master_action_interaction_after_A_ck_triad" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
