import ToeFormal.Derivation.PsiAInteractionExchangeTheoremLinkageChainCloseoutResultReview

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
  PsiAInteractionExchangeTheoremLinkageChainCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAInteractionExchangeTheoremLinkageChainCloseoutResultReview.packetId

theorem current_target_points_to_post_psi_A_exchange_chain_closeout_selector :
    currentLiveTarget =
      "select_next_ck_family_theorem_linkage_obligation_after_psi_A_exchange_chain_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
