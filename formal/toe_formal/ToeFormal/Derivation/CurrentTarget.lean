import ToeFormal.Derivation.PhiSourceTheoremLinkageObligationCloseoutResultReview

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

set_option linter.style.longLine false

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  PhiSourceTheoremLinkageObligationCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiSourceTheoremLinkageObligationCloseoutResultReview.packetId

theorem current_target_points_to_post_phi_source_closeout_selector :
    currentLiveTarget =
      "select_next_ck_family_theorem_linkage_obligation_after_phi_source_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
