import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterCExchangeCloseout

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
  CKFamilyTheoremLinkageObligationSelectionAfterCExchangeCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterCExchangeCloseout.packetId

theorem current_target_points_to_ck_selection_after_cexchange_closeout_review :
    currentLiveTarget =
      "review_ck_family_theorem_linkage_obligation_selection_after_cexchange_closeout_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
