import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPsiAExchangeChainCloseout

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
  CKFamilyTheoremLinkageObligationSelectionAfterPsiAExchangeChainCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterPsiAExchangeChainCloseout.packetId

theorem current_target_points_to_post_psi_A_exchange_chain_closeout_selector_review :
    currentLiveTarget =
      "review_ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
