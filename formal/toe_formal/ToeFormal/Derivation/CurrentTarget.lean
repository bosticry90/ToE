import ToeFormal.Derivation.PsiATotalConservationTheoremLinkageObligationCloseout

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
  PsiATotalConservationTheoremLinkageObligationCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiATotalConservationTheoremLinkageObligationCloseout.packetId

theorem current_target_points_to_psi_A_total_conservation_closeout_result_review :
    currentLiveTarget =
      "review_psi_A_total_conservation_theorem_linkage_obligation_closeout_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
