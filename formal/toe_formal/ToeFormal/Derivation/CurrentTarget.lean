import ToeFormal.Derivation.PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRoute

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
  PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRoute.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRoute.packetId

theorem current_target_points_to_gauge_exchange_attempt_result_review :
    currentLiveTarget =
      "review_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
