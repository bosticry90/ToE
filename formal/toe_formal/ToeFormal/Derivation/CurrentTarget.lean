import ToeFormal.Derivation.MasterActionCKFamilyGapReviewAfterPhiAAndPsiAResultReview

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
  MasterActionCKFamilyGapReviewAfterPhiAAndPsiAResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionCKFamilyGapReviewAfterPhiAAndPsiAResultReview.packetId

theorem current_target_points_to_selector_after_master_action_ck_family_gap_review_result :
    currentLiveTarget =
      "select_next_master_action_surface_after_ck_family_gap_review" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
