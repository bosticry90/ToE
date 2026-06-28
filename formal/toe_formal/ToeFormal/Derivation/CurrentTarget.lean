import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterPsiATotalConservationCloseout

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
  CKFamilyTheoremLinkageObligationSelectionAfterPsiATotalConservationCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterPsiATotalConservationCloseout.packetId

theorem current_target_points_to_post_psi_A_total_conservation_closeout_selector_review :
    currentLiveTarget =
      "review_ck_family_theorem_linkage_obligation_selection_after_" ++
        "psi_A_total_conservation_closeout_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
