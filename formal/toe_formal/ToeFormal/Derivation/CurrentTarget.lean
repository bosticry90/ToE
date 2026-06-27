import ToeFormal.Derivation.CExchangeTheoremLinkageAttemptFromTotalConservationRouteExecutionResultReview

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
  CExchangeTheoremLinkageAttemptFromTotalConservationRouteExecutionResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CExchangeTheoremLinkageAttemptFromTotalConservationRouteExecutionResultReview.packetId

theorem current_target_points_to_cexchange_theorem_linkage_obligation_closeout :
    currentLiveTarget =
      "prepare_cexchange_theorem_linkage_obligation_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
