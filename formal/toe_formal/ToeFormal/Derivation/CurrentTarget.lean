import ToeFormal.Derivation.MasterActionSurfaceSelectionAfterCKFamilyGapReview

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
  MasterActionSurfaceSelectionAfterCKFamilyGapReview.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionSurfaceSelectionAfterCKFamilyGapReview.packetId

theorem current_target_points_to_selector_result_review_after_master_action_ck_family_gap_review_selector :
    currentLiveTarget =
      "review_master_action_surface_selection_after_ck_family_gap_review_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
