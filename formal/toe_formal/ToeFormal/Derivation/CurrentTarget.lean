import ToeFormal.Derivation.CExchangeTheoremLinkageObligationCloseoutResultReview

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
  CExchangeTheoremLinkageObligationCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CExchangeTheoremLinkageObligationCloseoutResultReview.packetId

theorem current_target_points_to_ck_theorem_linkage_selector_after_cexchange_closeout :
    currentLiveTarget =
      "select_next_ck_family_theorem_linkage_obligation_after_cexchange_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
