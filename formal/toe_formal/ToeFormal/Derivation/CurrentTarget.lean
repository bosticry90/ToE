import ToeFormal.Derivation.PhiCKSourceBridgeTransportRuleFamilyCloseout

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
  PhiCKSourceBridgeTransportRuleFamilyCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiCKSourceBridgeTransportRuleFamilyCloseout.packetId

theorem current_target_points_to_next_master_action_surface_selector :
    currentLiveTarget =
      "select_next_master_action_surface_after_phi_ck_triad" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
