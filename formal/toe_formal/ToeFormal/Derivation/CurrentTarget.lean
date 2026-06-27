import ToeFormal.Derivation.MasterActionSurfaceSelectionAfterCKFamilyGapReviewResultReview

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
  MasterActionSurfaceSelectionAfterCKFamilyGapReviewResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionSurfaceSelectionAfterCKFamilyGapReviewResultReview.packetId

theorem current_target_points_to_theorem_linkage_obligation_index_preparation_after_selector_result_review :
    currentLiveTarget =
      "prepare_ck_family_theorem_linkage_obligation_index" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
