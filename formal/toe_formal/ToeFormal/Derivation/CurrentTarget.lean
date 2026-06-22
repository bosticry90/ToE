import ToeFormal.Derivation.ToeNativeASourceAdmissibilityReviewForVacuumStressEnergyResultReview

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
  ToeNativeASourceAdmissibilityReviewForVacuumStressEnergyResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeASourceAdmissibilityReviewForVacuumStressEnergyResultReview.packetId

theorem current_target_points_to_a_vacuum_source_admissibility_identity_packet :
    currentLiveTarget =
      "prepare_toe_native_A_vacuum_source_admissibility_identity_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
