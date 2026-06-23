import ToeFormal.Derivation.ToeNativeASourceAdmissibilityReviewRetryAfterVacuumIdentityResultReview

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
  ToeNativeASourceAdmissibilityReviewRetryAfterVacuumIdentityResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeASourceAdmissibilityReviewRetryAfterVacuumIdentityResultReview.packetId

theorem current_target_points_to_a_route_selector_after_vacuum_source_admissibility :
    currentLiveTarget =
      "select_next_toe_native_A_route_after_vacuum_source_admissibility" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
