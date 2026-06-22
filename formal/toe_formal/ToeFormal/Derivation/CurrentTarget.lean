import ToeFormal.Derivation.ToeNativeASourceAdmissibilityReviewForVacuumStressEnergy

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
  ToeNativeASourceAdmissibilityReviewForVacuumStressEnergy.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeASourceAdmissibilityReviewForVacuumStressEnergy.packetId

theorem current_target_points_to_a_vacuum_source_admissibility_review_result :
    currentLiveTarget =
      "review_toe_native_A_source_admissibility_review_for_vacuum_stress_energy_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
