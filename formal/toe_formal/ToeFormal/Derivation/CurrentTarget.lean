import ToeFormal.Derivation.CExchangeTheoremLinkageObligationCloseout

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
  CExchangeTheoremLinkageObligationCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  CExchangeTheoremLinkageObligationCloseout.packetId

theorem current_target_points_to_cexchange_theorem_linkage_obligation_closeout_review :
    currentLiveTarget =
      "review_cexchange_theorem_linkage_obligation_closeout_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
