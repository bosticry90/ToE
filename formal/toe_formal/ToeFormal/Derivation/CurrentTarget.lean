import ToeFormal.Derivation.PsiAInteractionExchangeTheoremLinkageChainSynthesisAfterCexchangeTotalMatterAndGaugeCloseouts

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
  PsiAInteractionExchangeTheoremLinkageChainSynthesisAfterCexchangeTotalMatterAndGaugeCloseouts.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAInteractionExchangeTheoremLinkageChainSynthesisAfterCexchangeTotalMatterAndGaugeCloseouts.packetId

theorem current_target_points_to_psi_A_interaction_exchange_chain_synthesis_review :
    currentLiveTarget =
      "review_psi_A_interaction_exchange_theorem_linkage_chain_synthesis_after_" ++
        "cexchange_total_matter_and_gauge_closeouts_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
