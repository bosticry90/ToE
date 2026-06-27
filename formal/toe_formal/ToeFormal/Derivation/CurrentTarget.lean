import ToeFormal.Derivation.CExchangeTheoremLinkageAttemptFromTotalConservationRoute

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
  CExchangeTheoremLinkageAttemptFromTotalConservationRoute.selectedNextTarget

def currentEvidencePacketId : String :=
  CExchangeTheoremLinkageAttemptFromTotalConservationRoute.packetId

theorem current_target_points_to_cexchange_theorem_linkage_attempt_review :
    currentLiveTarget =
      "review_cexchange_theorem_linkage_attempt_from_total_conservation_route_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
