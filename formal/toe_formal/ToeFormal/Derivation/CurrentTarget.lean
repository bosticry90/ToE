import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterCExchangeCloseoutResultReview

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
  CKFamilyTheoremLinkageObligationSelectionAfterCExchangeCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterCExchangeCloseoutResultReview.packetId

theorem current_target_points_to_psi_A_total_conservation_obligation_packet :
    currentLiveTarget =
      "prepare_psi_A_total_conservation_theorem_linkage_obligation_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
