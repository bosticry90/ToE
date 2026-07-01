import ToeFormal.Derivation.PhiBridgeTheoremLinkageObligationPacketResultReview

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

set_option linter.style.longLine false

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  PhiBridgeTheoremLinkageObligationPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiBridgeTheoremLinkageObligationPacketResultReview.packetId

theorem current_target_points_to_phi_bridge_attempt_preparation :
    currentLiveTarget =
      "prepare_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
