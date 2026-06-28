import ToeFormal.Derivation.PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairExecutionResultReview

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
  PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairExecutionResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairExecutionResultReview.packetId

theorem current_target_points_to_psi_A_matter_exchange_obligation_closeout_preparation :
    currentLiveTarget =
      "prepare_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
