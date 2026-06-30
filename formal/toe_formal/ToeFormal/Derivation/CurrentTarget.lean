import ToeFormal.Derivation.ASourceTheoremLinkageObligationCloseoutResultReview

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
  ASourceTheoremLinkageObligationCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ASourceTheoremLinkageObligationCloseoutResultReview.packetId

theorem current_target_points_to_selector_after_A_source_closeout_review :
    currentLiveTarget =
      "select_next_ck_family_theorem_linkage_obligation_after_A_source_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
