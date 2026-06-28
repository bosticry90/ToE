import ToeFormal.Derivation.PsiAMatterSectorExchangeTheoremLinkageObligationCloseoutResultReview

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
  PsiAMatterSectorExchangeTheoremLinkageObligationCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAMatterSectorExchangeTheoremLinkageObligationCloseoutResultReview.packetId

theorem current_target_points_to_selector_after_psi_A_matter_exchange_closeout :
    currentLiveTarget =
      "select_next_ck_family_theorem_linkage_obligation_after_psi_A_matter_exchange_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
