import ToeFormal.Derivation.ToeNativeAVacuumSourceAdmissibilityIdentityResultReview

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
  ToeNativeAVacuumSourceAdmissibilityIdentityResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeAVacuumSourceAdmissibilityIdentityResultReview.packetId

theorem current_target_points_to_a_source_admissibility_retry_after_identity :
    currentLiveTarget =
      "prepare_toe_native_A_source_admissibility_review_retry_after_vacuum_identity" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
