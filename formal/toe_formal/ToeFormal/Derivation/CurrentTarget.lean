import ToeFormal.Derivation.PsiAMatterSectorExchangeTheoremLinkageObligationPacketResultReview

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
  PsiAMatterSectorExchangeTheoremLinkageObligationPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAMatterSectorExchangeTheoremLinkageObligationPacketResultReview.packetId

theorem current_target_points_to_psi_A_matter_exchange_attempt_preparation :
    currentLiveTarget =
      "prepare_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
