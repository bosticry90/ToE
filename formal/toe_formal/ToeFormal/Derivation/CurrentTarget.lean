import ToeFormal.Derivation.PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutes

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
  PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutes.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutes.packetId

theorem current_target_points_to_psi_A_total_conservation_attempt_review :
    currentLiveTarget =
      "review_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
