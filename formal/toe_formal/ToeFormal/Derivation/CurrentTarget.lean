import ToeFormal.Derivation.PsiAInteractionExchangeTheoremLinkageChainSynthesisResultReview

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
  PsiAInteractionExchangeTheoremLinkageChainSynthesisResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAInteractionExchangeTheoremLinkageChainSynthesisResultReview.packetId

theorem current_target_points_to_psi_A_interaction_exchange_chain_closeout_preparation :
    currentLiveTarget =
      "prepare_psi_A_interaction_exchange_theorem_linkage_chain_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
