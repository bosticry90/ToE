import ToeFormal.Derivation.PsiATotalConservationTheoremLinkageObligationCloseoutResultReview

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
  PsiATotalConservationTheoremLinkageObligationCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiATotalConservationTheoremLinkageObligationCloseoutResultReview.packetId

theorem current_target_points_to_post_psi_A_total_conservation_closeout_selector :
    currentLiveTarget =
      "select_next_ck_family_theorem_linkage_obligation_after_" ++
        "psi_A_total_conservation_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
