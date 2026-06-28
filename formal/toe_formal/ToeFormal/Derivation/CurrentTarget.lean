import ToeFormal.Derivation.PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPair

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
  PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPair.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPair.packetId

theorem current_target_points_to_psi_A_matter_exchange_attempt_review :
    currentLiveTarget =
      "review_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
