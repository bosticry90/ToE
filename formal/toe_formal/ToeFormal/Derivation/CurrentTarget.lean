import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseout

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
  CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseout.packetId

theorem current_target_points_to_selector_result_review_after_psi_A_matter_exchange_closeout :
    currentLiveTarget =
      "review_ck_family_theorem_linkage_obligation_selection_after_" ++
        "psi_A_matter_exchange_closeout_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
