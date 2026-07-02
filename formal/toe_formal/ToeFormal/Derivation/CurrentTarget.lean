import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPhiBridgeCloseout

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
  CKFamilyTheoremLinkageObligationSelectionAfterPhiBridgeCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterPhiBridgeCloseout.packetId

theorem current_target_points_to_phi_bridge_selector_result_review :
    currentLiveTarget =
      "review_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
